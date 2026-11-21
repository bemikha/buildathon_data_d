// Shopping Sessions pipeline (optimized: parallel parse + radix sort + mmap).
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <cstdlib>
#include <string>
#include <vector>
#include <array>
#include <algorithm>
#include <numeric>
#include <filesystem>
#include <thread>
#include <atomic>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
using namespace std;

static const int64_t MS_PER_DAY = 86400000LL;
// (MS_PER_MIN removed)
static const int64_t MS_PER_HOUR = 3600000LL;
static const int64_t SESSION_GAP = 1800000LL;      // 30 min
static const int64_t CLICK_REACH = 7 * MS_PER_DAY; // 7 days
static const int64_t LATE_LIMIT = 24 * MS_PER_HOUR; // 24 hours

// ---------- pack7 ----------
static uint64_t pack7(const char* s, int n) {
    const uint8_t* b = (const uint8_t*)s;
    uint64_t k = 0;
    int i = 0;
    switch (n) {
        default: return 0;
        case 9: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 8: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 7: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 6: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 5: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 4: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 3: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 2: k = (k << 7) | (b[i++] & 0x7F); [[fallthrough]];
        case 1: k = (k << 7) | (b[i++] & 0x7F); break;
    }
    while (i < 9) { k <<= 7; i++; }
    return k;
}
static string unpack7(uint64_t k) {
    char buf[9]; int len = 0;
    for (int i = 0; i < 9; i++) { char c = (char)((k >> (7 * (8 - i))) & 0x7F); if (c) buf[len++] = c; }
    return string(buf, len);
}

// ---------- calendar ----------
static bool is_leap(int64_t y) { return y % 4 == 0 && (y % 100 != 0 || y % 400 == 0); }
static int dim(int64_t y, int m) {
    static const int t[13] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
    if (m == 2 && is_leap(y)) return 29;
    return t[m];
}
static int64_t days_from_civil(int64_t y, int m, int d) {
    y -= m <= 2;
    int64_t era = (y >= 0 ? y : y - 399) / 400;
    unsigned yoe = (unsigned)(y - era * 400);
    unsigned doy = (153u * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + (int64_t)doe - 719468;
}
// Fast day-of-year path for the (almost constant) window year.
static int64_t g_base_year = 0, g_base_day = 0; static int g_base_leap = 0;
static const int cum[13] = {0,0,31,59,90,120,151,181,212,243,273,304,334};
static inline int64_t fast_days(int64_t y, int m, int d) {
    if (y == g_base_year)
        return g_base_day + cum[m] + d - 1 + (m > 2 ? g_base_leap : 0);
    return days_from_civil(y, m, d);
}
static inline bool all_digits(const char* s, int n) {
    for (int i = 0; i < n; i++) if (s[i] < '0' || s[i] > '9') return false;
    return n > 0;
}
static inline bool digits_to(const char* s, int n, int64_t& out) {
    int64_t v = 0;
    for (int i = 0; i < n; i++) { char c = s[i]; if (c < '0' || c > '9') return false; v = v * 10 + (c - '0'); }
    out = v; return true;
}
static int parse_ts(const char* s, int n, int64_t& out) {
    if (n == 20) {
        if (s[4] != '-' || s[7] != '-' || s[10] != 'T' || s[13] != ':' || s[16] != ':' || s[19] != 'Z') return 0;
        int64_t y, mo, d, h, mi, sec;
        if (!digits_to(s, 4, y) || !digits_to(s+5, 2, mo) || !digits_to(s+8, 2, d) ||
            !digits_to(s+11, 2, h) || !digits_to(s+14, 2, mi) || !digits_to(s+17, 2, sec)) return 0;
        if (mo < 1 || mo > 12) return 0;
        if (d < 1 || d > dim(y, (int)mo)) return 0;
        if (h > 23 || mi > 59 || sec > 59) return 0;
        out = fast_days(y, (int)mo, (int)d) * MS_PER_DAY + (h * 3600 + mi * 60 + sec) * 1000;
        return 1;
    }
    if (all_digits(s, n)) {
        uint64_t v = 0; bool overflow = false;
        for (int i = 0; i < n; i++) {
            int d = s[i] - '0';
            if (v > (UINT64_MAX - d) / 10) { overflow = true; break; }
            v = v * 10 + d;
        }
        if (overflow) { out = INT64_MAX; return 1; }
        out = (int64_t)v;
        return 1;
    }
    if (n == 25) {
        if (s[4] != '-' || s[7] != '-' || s[10] != 'T' || s[13] != ':' || s[16] != ':') return 0;
        if (s[22] != ':') return 0;
        int sign;
        if (s[19] == '+') sign = 1; else if (s[19] == '-') sign = -1; else return 0;
        int64_t y, mo, d, h, mi, sec, oh, om;
        if (!digits_to(s, 4, y) || !digits_to(s+5, 2, mo) || !digits_to(s+8, 2, d) ||
            !digits_to(s+11, 2, h) || !digits_to(s+14, 2, mi) || !digits_to(s+17, 2, sec) ||
            !digits_to(s+20, 2, oh) || !digits_to(s+23, 2, om)) return 0;
        if (mo < 1 || mo > 12) return 0;
        if (d < 1 || d > dim(y, (int)mo)) return 0;
        if (h > 23 || mi > 59 || sec > 59) return 0;
        if (oh > 23 || om > 59) return 0;
        out = fast_days(y, (int)mo, (int)d) * MS_PER_DAY + (h * 3600 + mi * 60 + sec) * 1000 - sign * (oh * 60 + om) * 60000;
        return 1;
    }
    return 0;
}

// ---------- CSV splitting ----------
struct Field { const char* p; int n; };
// SWAR search for the first byte equal to `a` or `b` at/after i (b==0 disables it).
static inline size_t find_delim(const char* s, size_t i, size_t n, uint8_t a, uint8_t b) {
    const uint64_t ones = 0x0101010101010101ULL;
    const uint64_t hi   = 0x8080808080808080ULL;
    const uint64_t pa = (uint64_t)a * ones, pb = (uint64_t)b * ones;
    while (i + 8 <= n) {
        uint64_t w; memcpy(&w, s + i, 8);
        uint64_t x = w ^ pa;
        uint64_t c = (x - ones) & ~x & hi;
        uint64_t m = c;
        if (b) { uint64_t y = w ^ pb; m |= (y - ones) & ~y & hi; }
        if (m) return i + ((size_t)__builtin_ctzll(m) >> 3);
        i += 8;
    }
    while (i < n && s[i] != a && (!b || s[i] != b)) i++;
    return i;
}
static inline int split_line(const char* s, int n, Field* f, int maxf) {
    if (n == 0) return -1;
    int cnt = 0; size_t i = 0;
    while (true) {
        if (cnt >= maxf) return -1;
        if (i < (size_t)n && s[i] == '"') {
            i++; size_t st = i;
            i = find_delim(s, i, (size_t)n, '"', 0);
            if (i >= (size_t)n) return -1;
            f[cnt].p = s + st; f[cnt].n = (int)(i - st); cnt++;
            i++;
            if (i < (size_t)n) { if (s[i] != ',') return -1; i++; } else break;
        } else {
            size_t st = i;
            i = find_delim(s, i, (size_t)n, ',', '"');
            if (i < (size_t)n && s[i] == '"') return -1;
            f[cnt].p = s + st; f[cnt].n = (int)(i - st); cnt++;
            if (i < (size_t)n) i++; else break;
        }
    }
    return cnt == maxf ? cnt : -1;
}

// ---------- parallel helpers ----------
template <typename F>
static void parallel_for(int nt, size_t n, F f) {
    if (nt <= 1 || n < 4096) { f(0, 0, n); return; }
    if ((size_t)nt > n) nt = (int)n;
    size_t chunk = (n + nt - 1) / nt;
    vector<thread> ts; ts.reserve(nt);
    for (int t = 0; t < nt; t++) {
        size_t lo = (size_t)t * chunk, hi = lo + chunk;
        if (hi > n) hi = n;
        if (lo >= hi) break;
        ts.emplace_back([&, t, lo, hi]() { f(t, lo, hi); });
    }
    for (auto& th : ts) th.join();
}

// ---------- parallel radix sort (LSD, stable) ----------
template <typename T, typename KF>
static void radix_sort(vector<T>& a, KF keyf, int nt, int npass = 5) {
    size_t n = a.size();
    if (n < 2) return;
    vector<T> tmp(n);
    const int BITS = 13, BUCKETS = 1 << BITS, MASK = BUCKETS - 1;
    vector<uint32_t> hist((size_t)nt * BUCKETS, 0);
    for (int pass = 0; pass < npass; pass++) {
        int shift = pass * BITS;
        for (auto& x : hist) x = 0;
        parallel_for(nt, n, [&](int tid, size_t lo, size_t hi) {
            uint32_t* h = &hist[(size_t)tid * BUCKETS];
            for (size_t i = lo; i < hi; i++) h[(keyf(a[i]) >> shift) & MASK]++;
        });
        uint32_t total = 0;
        for (int b = 0; b < BUCKETS; b++)
            for (int t = 0; t < nt; t++) {
                uint32_t c = hist[(size_t)t * BUCKETS + b];
                hist[(size_t)t * BUCKETS + b] = total;
                total += c;
            }
        parallel_for(nt, n, [&](int tid, size_t lo, size_t hi) {
            uint32_t run[BUCKETS];
            for (int b = 0; b < BUCKETS; b++) run[b] = hist[(size_t)tid * BUCKETS + b];
            for (size_t i = lo; i < hi; i++) {
                int b = (keyf(a[i]) >> shift) & MASK;
                tmp[run[b]++] = std::move(a[i]);
            }
        });
        a.swap(tmp);
    }
}

// ---------- mmap ----------
struct MappedFile { int fd = -1; const char* p = nullptr; size_t n = 0; };
static bool map_open(MappedFile& m, const string& path) {
    m.fd = ::open(path.c_str(), O_RDONLY);
    if (m.fd < 0) return false;
    struct stat st; fstat(m.fd, &st);
    m.n = (size_t)st.st_size;
    m.p = (const char*)mmap(nullptr, m.n, PROT_READ, MAP_PRIVATE, m.fd, 0);
    return m.p != MAP_FAILED;
}
static void map_close(MappedFile& m) {
    if (m.p && m.p != MAP_FAILED) munmap((void*)m.p, m.n);
    if (m.fd >= 0) ::close(m.fd);
    m.p = nullptr; m.fd = -1;
}

// Generic parallel file parser.
template <typename T, typename PF>
static vector<T> parse_all(const vector<string>& files, PF parse_one, int nt, size_t avg_line) {
    vector<vector<T>> per(nt);
    {
        size_t total_bytes = 0;
        for (auto& f : files) { struct stat st; if (stat(f.c_str(), &st) == 0) total_bytes += (size_t)st.st_size; }
        size_t est = total_bytes / (avg_line ? avg_line : 1);
        for (auto& v : per) v.reserve(est / nt + est / (nt * 2) + 64);
    }
    atomic<size_t> next{0};
    vector<thread> ts; ts.reserve(nt);
    for (int t = 0; t < nt; t++) {
        ts.emplace_back([&, t]() {
            while (true) {
                size_t fi = next.fetch_add(1);
                if (fi >= files.size()) break;
                MappedFile m;
                if (!map_open(m, files[fi])) continue;
                parse_one(m.p, m.n, per[t]);
                map_close(m);
            }
        });
    }
    for (auto& th : ts) th.join();
    size_t total = 0;
    for (auto& v : per) total += v.size();
    vector<T> out; out.reserve(total);
    for (auto& v : per) out.insert(out.end(), v.begin(), v.end());
    return out;
}

// ---------- Parquet writer ----------
struct Thrift {
    vector<uint8_t> b;
    void varint(uint64_t v) { while (v >= 0x80) { b.push_back(0x80 | (v & 0x7F)); v >>= 7; } b.push_back((uint8_t)v); }
    void zig32(int32_t v) { varint((uint32_t)((v << 1) ^ (v >> 31))); }
    void zig64(int64_t v) { varint((uint64_t)((v << 1) ^ (v >> 63))); }
    void fld(int fid_delta, int type) { b.push_back((uint8_t)((fid_delta << 4) | type)); }
    void stop() { b.push_back(0); }
    void i32f(int delta, int32_t v) { fld(delta, 5); zig32(v); }
    void i64f(int delta, int64_t v) { fld(delta, 6); zig64(v); }
    void strf(int delta, const string& s) { fld(delta, 8); varint(s.size()); b.insert(b.end(), s.begin(), s.end()); }
    void strf(int delta, const char* s, size_t n) { fld(delta, 8); varint(n); b.insert(b.end(), s, s + n); }
};
struct ColSpec {
    string name;
    int ptype;
    bool optional;
    int converted;
    vector<uint8_t> data;
    vector<uint8_t> nulls;
};
static vector<uint8_t> rle_defl(const vector<uint8_t>& present, int num_values) {
    int groups = (num_values + 7) / 8;
    vector<uint8_t> body;
    Thrift t; t.varint((uint64_t)((groups << 1) | 1));
    body.insert(body.end(), t.b.begin(), t.b.end());
    body.resize(body.size() + groups, 0);
    for (int i = 0; i < num_values; i++) if (present[i]) body[body.size() - groups + (i >> 3)] |= (uint8_t)(1 << (i & 7));
    vector<uint8_t> out;
    uint32_t len = (uint32_t)body.size();
    out.push_back(len & 0xFF); out.push_back((len >> 8) & 0xFF); out.push_back((len >> 16) & 0xFF); out.push_back((len >> 24) & 0xFF);
    out.insert(out.end(), body.begin(), body.end());
    return out;
}
static void write_parquet(const string& path, const vector<ColSpec>& cols, int64_t num_rows) {
    vector<uint8_t> file = {'P','A','R','1'};
    vector<int64_t> data_page_offset(cols.size());
    vector<int64_t> total_uncomp(cols.size());
    for (size_t c = 0; c < cols.size(); c++) {
        const ColSpec& col = cols[c];
        data_page_offset[c] = (int64_t)file.size();
        vector<uint8_t> page_data;
        if (col.optional) {
            vector<uint8_t> dl = rle_defl(col.nulls, (int)num_rows);
            page_data.insert(page_data.end(), dl.begin(), dl.end());
        }
        page_data.insert(page_data.end(), col.data.begin(), col.data.end());
        Thrift ph;
        ph.i32f(1, 0);
        ph.i32f(1, (int32_t)page_data.size());
        ph.i32f(1, (int32_t)page_data.size());
        ph.fld(2, 12);
        ph.i32f(1, (int32_t)num_rows);
        ph.i32f(1, 0);
        ph.i32f(1, 3);
        ph.i32f(1, 3);
        ph.stop();
        ph.stop();
        file.insert(file.end(), ph.b.begin(), ph.b.end());
        file.insert(file.end(), page_data.begin(), page_data.end());
        total_uncomp[c] = (int64_t)(ph.b.size() + page_data.size());
    }
    Thrift fm;
    fm.i32f(1, 1);
    fm.fld(1, 9); fm.b.push_back((uint8_t)(((cols.size() + 1) << 4) | 12));
    { fm.i32f(3, 0); fm.strf(1, "schema"); fm.i32f(1, (int32_t)cols.size()); fm.stop(); }
    for (auto& col : cols) {
        fm.i32f(1, col.ptype);
        fm.i32f(2, col.optional ? 1 : 0);
        fm.strf(1, col.name);
        if (col.converted >= 0) fm.i32f(2, col.converted);
        fm.stop();
    }
    fm.i64f(1, num_rows);
    fm.fld(1, 9); fm.b.push_back((uint8_t)((1 << 4) | 12));
    {
        fm.fld(1, 9); fm.b.push_back((uint8_t)((cols.size() << 4) | 12));
        int64_t total_byte = 0;
        for (size_t c = 0; c < cols.size(); c++) {
            const ColSpec& col = cols[c];
            total_byte += total_uncomp[c];
            fm.i64f(2, data_page_offset[c]);
            fm.fld(1, 12);
            fm.i32f(1, col.ptype);
            fm.fld(1, 9); fm.b.push_back((uint8_t)((2 << 4) | 5));
            fm.zig32(3); fm.zig32(0);
            fm.fld(1, 9); fm.b.push_back((uint8_t)((1 << 4) | 8));
            fm.varint(col.name.size()); fm.b.insert(fm.b.end(), col.name.begin(), col.name.end());
            fm.i32f(1, 0);
            fm.i64f(1, num_rows);
            fm.i64f(1, total_uncomp[c]);
            fm.i64f(1, total_uncomp[c]);
            fm.i64f(2, data_page_offset[c]);
            fm.stop();
            fm.stop();
        }
        fm.i64f(1, total_byte);
        fm.i64f(1, num_rows);
        fm.stop();
    }
    fm.stop();
    file.insert(file.end(), fm.b.begin(), fm.b.end());
    uint32_t flen = (uint32_t)fm.b.size();
    file.push_back(flen & 0xFF); file.push_back((flen >> 8) & 0xFF); file.push_back((flen >> 16) & 0xFF); file.push_back((flen >> 24) & 0xFF);
    file.push_back('P'); file.push_back('A'); file.push_back('R'); file.push_back('1');
    FILE* f = fopen(path.c_str(), "wb");
    fwrite(file.data(), 1, file.size(), f);
    fclose(f);
}

// ---------- main ----------
int main(int argc, char** argv) {
    string data = "/data", out = "/output";
    if (argc >= 3) { data = argv[1]; out = argv[2]; }

    int nt = 8;
    if (const char* e = getenv("NCPU")) { int v = atoi(e); if (v >= 1 && v <= 128) nt = v; }

    // manifest
    string manifest;
    { FILE* f = fopen((data + "/manifest.json").c_str(), "rb"); char buf[4096]; size_t n = fread(buf, 1, sizeof(buf), f); fclose(f); manifest.assign(buf, n); }
    auto find_str = [&](const string& key) {
        size_t p = manifest.find("\"" + key + "\"");
        p = manifest.find("\"", p + key.size() + 2);
        size_t e = manifest.find("\"", p + 1);
        return manifest.substr(p + 1, e - p - 1);
    };
    string ws = find_str("window_start"), we = find_str("window_end");
    int64_t window_start, window_end;
    parse_ts(ws.c_str(), (int)ws.size(), window_start);
    parse_ts(we.c_str(), (int)we.size(), window_end);
    int64_t click_window_start = window_start - CLICK_REACH;
    int64_t base_day = window_start / MS_PER_DAY;
    int64_t key_base = window_start - CLICK_REACH;
    // Set the fast date base from the manifest year ("YYYY-..."); falls back to
    // the generic algorithm for any timestamp in a different year.
    if (ws.size() >= 5 && ws[4] == '-' && ws[0] >= '0' && ws[0] <= '9' && ws[1] >= '0' && ws[1] <= '9' && ws[2] >= '0' && ws[2] <= '9' && ws[3] >= '0' && ws[3] <= '9') {
        g_base_year = (ws[0]-'0') * 1000 + (ws[1]-'0') * 100 + (ws[2]-'0') * 10 + (ws[3]-'0');
        g_base_day = days_from_civil(g_base_year, 1, 1);
        g_base_leap = is_leap(g_base_year) ? 1 : 0;
    }
    int32_t win_off_start = (int32_t)CLICK_REACH;                 // 7 days
    int32_t win_off_end = (int32_t)(window_end - key_base);       // 21 days

    // products & campaigns
    array<uint8_t, 50001> cat; cat.fill(20);
    array<uint8_t, 2001> chan; chan.fill(255);
    {
        auto read_lines = [&](const string& path, auto fn) {
            FILE* f = fopen(path.c_str(), "rb");
            fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
            vector<char> buf(sz + 1); fread(buf.data(), 1, sz, f); fclose(f);
            buf[sz] = 0;
            char* line = buf.data();
            bool first = true;
            for (char* p = buf.data(); ; p++) {
                if (*p == '\n' || *p == 0) {
                    int n = (int)(p - line);
                    if (!first) fn(line, n);
                    first = false;
                    if (*p == 0) break;
                    line = p + 1;
                }
            }
        };
        static const char* cats[20] = {"apparel","automotive","baby","beauty","books","electronics","garden","grocery","home","jewelry","kitchen","music","office","outdoors","pets","shoes","sports","tools","toys","video_games"};
        read_lines(data + "/products.csv", [&](char* line, int n) {
            char* c = (char*)memchr(line, ',', n);
            if (!c) return;
            int idn = (int)(c - line);
            int pid = atoi(string(line + 1, idn - 1).c_str());
            string cn(c + 1, n - idn - 1);
            int idx = -1;
            for (int i = 0; i < 20; i++) if (cn == cats[i]) { idx = i; break; }
            if (pid >= 1 && pid <= 50000 && idx >= 0) cat[pid] = (uint8_t)idx;
        });
        static const char* chans[5] = {"affiliate","display","email","search","social"};
        read_lines(data + "/campaigns.csv", [&](char* line, int n) {
            char* c = (char*)memchr(line, ',', n);
            if (!c) return;
            int idn = (int)(c - line);
            int cid = atoi(string(line + 2, idn - 2).c_str());
            string ch(c + 1, n - idn - 1);
            int idx = -1;
            for (int i = 0; i < 5; i++) if (ch == chans[i]) { idx = i; break; }
            if (cid >= 1 && cid <= 2000 && idx >= 0) chan[cid] = (uint8_t)idx;
        });
    }

    auto list_files = [&](const string& dir) {
        vector<string> v;
        for (auto& e : filesystem::directory_iterator(dir)) if (e.is_regular_file()) v.push_back(e.path().string());
        sort(v.begin(), v.end());
        return v;
    };

    // ---------- parse events (parallel) ----------
    // ts_off    = ts       - key_base (i32; valid in-window ts is +[7d,21d]).
    // ingest_off= ingest_ts- key_base (i32; saturating cast is safe: copies of a
    //   duplicate are strictly later, so a saturated group still keeps the earliest).
    struct Event { uint64_t event_id, user_id; int32_t ts_off, ingest_off; int32_t price; uint16_t cat; uint8_t type, flags; };
    auto parse_events_file = [&](const char* buf, size_t sz, vector<Event>& out) {
        const char* p = buf; const char* end = buf + sz;
        const char* nl = (const char*)memchr(p, '\n', (size_t)(end - p));
        if (!nl) return;
        p = nl + 1;
        Field f[7];
        while (p < end) {
            const char* e = (const char*)memchr(p, '\n', (size_t)(end - p));
            const char* le = e ? e : end;
            int n = (int)(le - p);
            if (n > 0 && split_line(p, n, f, 7) == 7) {
                if (f[0].n != 0) {
                    Event ev{};
                    ev.event_id = pack7(f[0].p, f[0].n);
                    ev.user_id = pack7(f[1].p, f[1].n);
                    int64_t ts = 0; int tsv = parse_ts(f[2].p, f[2].n, ts);
                    int64_t ingest = 0; parse_ts(f[3].p, f[3].n, ingest);
                    int64_t to = ts - key_base;
                    ev.ts_off = (int32_t)(to < INT32_MIN ? INT32_MIN : (to > INT32_MAX ? INT32_MAX : to));
                    int64_t io = ingest - key_base;
                    ev.ingest_off = (int32_t)(io < INT32_MIN ? INT32_MIN : (io > INT32_MAX ? INT32_MAX : io));
                    ev.type = 3;
                    if (f[4].n == 4 && memcmp(f[4].p, "view", 4) == 0) ev.type = 0;
                    else if (f[4].n == 4 && memcmp(f[4].p, "cart", 4) == 0) ev.type = 1;
                    else if (f[4].n == 8 && memcmp(f[4].p, "purchase", 8) == 0) ev.type = 2;
                    ev.cat = 20;
                    if (f[5].n >= 2 && f[5].p[0] == 'p' && f[5].p[1] != '0') {
                        int64_t pid = 0; bool ok = true;
                        for (int i = 1; i < f[5].n; i++) { char c = f[5].p[i]; if (c < '0' || c > '9') { ok = false; break; } pid = pid * 10 + (c - '0'); if (pid > 50000) { ok = false; break; } }
                        if (ok && pid >= 1 && pid <= 50000) ev.cat = cat[(int)pid];
                    }
                    ev.price = 0;
                    bool price_ok = true;
                    if (ev.type == 2) {
                        int64_t pr = 0;
                        if (f[6].n == 0) price_ok = false;
                        else {
                            for (int i = 0; i < f[6].n; i++) { char c = f[6].p[i]; if (c < '0' || c > '9') { price_ok = false; break; } pr = pr * 10 + (c - '0'); if (pr > 10000000) { price_ok = false; break; } }
                            if (pr < 1 || pr > 10000000) price_ok = false;
                            if (price_ok) ev.price = (int32_t)pr;
                        }
                    }
                    ev.flags = 0;
                    if (tsv && ev.ts_off >= win_off_start && ev.ts_off < win_off_end) ev.flags |= 1;
                    if (f[1].n > 0) ev.flags |= 2;
                    if (ev.type != 3) ev.flags |= 4;
                    if (f[5].n > 0) ev.flags |= 8;
                    if (ev.type != 2 || price_ok) ev.flags |= 16;
                    if ((int64_t)ev.ingest_off - (int64_t)ev.ts_off <= LATE_LIMIT) ev.flags |= 32;
                    out.push_back(ev);
                }
            }
            if (!e) break;
            p = e + 1;
        }
    };

    // ---------- parse clicks (parallel) ----------
    struct Click { uint64_t click_id, user_id; int64_t ts; uint32_t campaign; uint32_t flags; };
    auto parse_clicks_file = [&](const char* buf, size_t sz, vector<Click>& out) {
        const char* p = buf; const char* end = buf + sz;
        const char* nl = (const char*)memchr(p, '\n', (size_t)(end - p));
        if (!nl) return;
        p = nl + 1;
        Field f[4];
        while (p < end) {
            const char* e = (const char*)memchr(p, '\n', (size_t)(end - p));
            const char* le = e ? e : end;
            int n = (int)(le - p);
            if (n > 0 && split_line(p, n, f, 4) == 4) {
                if (f[0].n != 0) {
                    Click c{};
                    c.click_id = pack7(f[0].p, f[0].n);
                    c.user_id = pack7(f[1].p, f[1].n);
                    int64_t ts = 0; int tsv = parse_ts(f[3].p, f[3].n, ts); c.ts = ts;
                    c.campaign = 0xFFFFFFFF;
                    if (f[2].n >= 3 && f[2].p[0] == 'c' && f[2].p[1] == '_' && f[2].p[2] != '0') {
                        int64_t cidn = 0; bool ok = true;
                        for (int i = 2; i < f[2].n; i++) { char cc = f[2].p[i]; if (cc < '0' || cc > '9') { ok = false; break; } cidn = cidn * 10 + (cc - '0'); if (cidn > 2000) { ok = false; break; } }
                        if (ok && cidn >= 1 && cidn <= 2000 && chan[(int)cidn] != 255) c.campaign = (uint32_t)(cidn - 1);
                    }
                    c.flags = 0;
                    if (tsv && ts >= click_window_start && ts < window_end) c.flags |= 1;
                    if (f[1].n > 0) c.flags |= 2;
                    if (c.campaign != 0xFFFFFFFF) c.flags |= 4;
                    out.push_back(c);
                }
            }
            if (!e) break;
            p = e + 1;
        }
    };

    // ---------- parse links (parallel) ----------
    auto parse_links_file = [&](const char* buf, size_t sz, vector<pair<uint64_t,uint64_t>>& out) {
        const char* p = buf; const char* end = buf + sz;
        const char* nl = (const char*)memchr(p, '\n', (size_t)(end - p));
        if (!nl) return;
        p = nl + 1;
        Field f[2];
        while (p < end) {
            const char* e = (const char*)memchr(p, '\n', (size_t)(end - p));
            const char* le = e ? e : end;
            int n = (int)(le - p);
            if (n > 0 && split_line(p, n, f, 2) == 2) {
                if (f[0].n > 0 && f[1].n > 0) out.emplace_back(pack7(f[0].p, f[0].n), pack7(f[1].p, f[1].n));
            }
            if (!e) break;
            p = e + 1;
        }
    };

    vector<string> event_files = list_files(data + "/events");
    vector<string> click_files = list_files(data + "/clicks");
    vector<string> link_files = list_files(data + "/links");

    // Parse in parallel: events, clicks, links (each group uses its own threads).
    vector<Event> events = parse_all<Event>(event_files, parse_events_file, nt, 80);
    vector<Click> clicks = parse_all<Click>(click_files, parse_clicks_file, nt, 50);
    vector<pair<uint64_t,uint64_t>> links = parse_all<pair<uint64_t,uint64_t>>(link_files, parse_links_file, nt, 20);

    // ---------- events dedup (keep min ingest_ts) + validate + compact (24B) ----------
    // E drops event_id/ingest_ts/flags after dedup; user_id (u64) is later replaced
    // by the dense person id (u32), layout-compatible with Ev.
    struct E { uint64_t user_id; int64_t ts; uint8_t type, category; int32_t price; };
    radix_sort(events, [](const Event& e){ return e.event_id; }, nt);
    vector<E> es;
    {
        size_t i = 0, n = events.size();
        es.reserve(n);
        while (i < n) {
            size_t j = i, best = i;
            while (j < n && events[j].event_id == events[i].event_id) {
                if (events[j].ingest_off < events[best].ingest_off) best = j;
                j++;
            }
            const Event& e = events[best];
            if ((e.flags & 0x1F) == 0x1F && (e.flags & 32)) {
                es.push_back({e.user_id, (int64_t)e.ts_off + key_base, e.type, (uint8_t)e.cat, e.price});
            }
            i = j;
        }
        events.clear(); events.shrink_to_fit();
    }

    // ---------- clicks dedup (keep first) + validate ----------
    radix_sort(clicks, [](const Click& c){ return c.click_id; }, nt);
    {
        size_t w = 0, i = 0, n = clicks.size();
        while (i < n) {
            size_t j = i;
            while (j < n && clicks[j].click_id == clicks[i].click_id) j++;
            const Click& c = clicks[i];
            if ((c.flags & 0x07) == 0x07) clicks[w++] = c;
            i = j;
        }
        clicks.resize(w);
    }

    // ---------- interning: collect all user_ids, sort, unique ----------
    size_t nL = links.size(), nE = es.size(), nC = clicks.size();
    vector<uint64_t> all_ids(2 * nL + nE + nC);
    parallel_for(nt, 2 * nL, [&](int, size_t lo, size_t hi) {
        for (size_t i = lo; i < hi; i++) all_ids[i] = (i & 1) ? links[i >> 1].second : links[i >> 1].first;
    });
    parallel_for(nt, nE, [&](int, size_t lo, size_t hi) {
        for (size_t i = lo; i < hi; i++) all_ids[2 * nL + i] = es[i].user_id;
    });
    parallel_for(nt, nC, [&](int, size_t lo, size_t hi) {
        for (size_t i = lo; i < hi; i++) all_ids[2 * nL + nE + i] = clicks[i].user_id;
    });
    radix_sort(all_ids, [](uint64_t x){ return x; }, nt);
    all_ids.erase(unique(all_ids.begin(), all_ids.end()), all_ids.end());
    int K = (int)all_ids.size();

    // sort-merge assign indices (parallel: each chunk finds its start via lower_bound)
    auto* all_ids_b = all_ids.data();
    radix_sort(links, [](const pair<uint64_t,uint64_t>& l){ return l.first; }, nt);
    if (!links.empty()) parallel_for(nt, links.size(), [&](int, size_t lo, size_t hi) {
        size_t d = (size_t)(lower_bound(all_ids_b, all_ids_b + all_ids.size(), links[lo].first) - all_ids_b);
        for (size_t i = lo; i < hi; i++) { while (all_ids_b[d] < links[i].first) d++; links[i].first = (uint32_t)d; }
    });
    radix_sort(links, [](const pair<uint64_t,uint64_t>& l){ return l.second; }, nt);
    if (!links.empty()) parallel_for(nt, links.size(), [&](int, size_t lo, size_t hi) {
        size_t d = (size_t)(lower_bound(all_ids_b, all_ids_b + all_ids.size(), links[lo].second) - all_ids_b);
        for (size_t i = lo; i < hi; i++) { while (all_ids_b[d] < links[i].second) d++; links[i].second = (uint32_t)d; }
    });

    radix_sort(es, [](const E& e){ return e.user_id; }, nt);
    if (!es.empty()) parallel_for(nt, es.size(), [&](int, size_t lo, size_t hi) {
        size_t d = (size_t)(lower_bound(all_ids_b, all_ids_b + all_ids.size(), es[lo].user_id) - all_ids_b);
        for (size_t i = lo; i < hi; i++) { while (all_ids_b[d] < es[i].user_id) d++; es[i].user_id = (uint32_t)d; }
    });
    radix_sort(clicks, [](const Click& c){ return c.user_id; }, nt);
    if (!clicks.empty()) parallel_for(nt, clicks.size(), [&](int, size_t lo, size_t hi) {
        size_t d = (size_t)(lower_bound(all_ids_b, all_ids_b + all_ids.size(), clicks[lo].user_id) - all_ids_b);
        for (size_t i = lo; i < hi; i++) { while (all_ids_b[d] < clicks[i].user_id) d++; clicks[i].user_id = (uint32_t)d; }
    });

    // union-find
    vector<int> parent(K);
    iota(parent.begin(), parent.end(), 0);
    {
        auto find = [&](int x) { while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; };
        for (auto& l : links) {
            int ra = find((int)l.first), rb = find((int)l.second);
            if (ra != rb) parent[ra] = rb;
        }
        vector<uint64_t> minv(K, UINT64_MAX);
        for (int i = 0; i < K; i++) { int r = find(i); if (all_ids[i] < minv[r]) minv[r] = all_ids[i]; }
        vector<uint32_t> root_dense(K, UINT32_MAX);
        int P = 0;
        for (int i = 0; i < K; i++) { int r = find(i); if (root_dense[r] == UINT32_MAX) root_dense[r] = P++; }
        // (person << 32 | ts) sort needs ceil((32 + bits(person)) / 13) passes.
        int npass_person = 5;
        { uint32_t x = (uint32_t)(P > 0 ? P - 1 : 0); int b = 0; while (x) { b++; x >>= 1; }
          int np = (32 + b + 12) / 13; if (np < 1) np = 1; if (np < 5) npass_person = np; }
        vector<uint32_t> person_of(K);
        for (int i = 0; i < K; i++) person_of[i] = root_dense[find(i)];
        vector<string> person_name(P);
        for (int i = 0; i < K; i++) { int r = find(i); if (minv[r] == all_ids[i]) person_name[root_dense[r]] = unpack7(all_ids[i]); }

        // map events/clicks idx -> person
        parallel_for(nt, es.size(), [&](int, size_t lo, size_t hi) {
            for (size_t i = lo; i < hi; i++) es[i].user_id = person_of[(uint32_t)es[i].user_id];
        });
        parallel_for(nt, clicks.size(), [&](int, size_t lo, size_t hi) {
            for (size_t i = lo; i < hi; i++) clicks[i].user_id = person_of[(uint32_t)clicks[i].user_id];
        });

        // ---------- sessionize ----------
        // es[i].user_id now holds the u32 person in its low 32 bits (little-endian).
        radix_sort(es, [&](const E& e){ return ((uint64_t)(uint32_t)e.user_id << 32) | (uint32_t)(e.ts - key_base); }, nt, npass_person);

        struct Session { uint32_t person; int32_t day; int64_t start; uint32_t events; uint32_t has_purchase; int64_t revenue; };
        struct Purch { uint32_t person; int32_t day; uint8_t category; int64_t price; };
        vector<Session> sessions;
        vector<Purch> purchs;
        {
            size_t n = es.size();
            vector<size_t> pstart; pstart.reserve(1 << 20);
            pstart.push_back(0);
            for (size_t i = 1; i < n; i++) if ((uint32_t)es[i].user_id != (uint32_t)es[i-1].user_id) pstart.push_back(i);
            size_t np = pstart.size();
            vector<vector<Session>> psess(nt);
            vector<vector<Purch>> ppurch(nt);
            parallel_for(nt, np, [&](int tid, size_t lo, size_t hi) {
                auto& outs = psess[tid]; auto& outp = ppurch[tid];
                for (size_t r = lo; r < hi; r++) {
                    size_t s = pstart[r];
                    size_t e = (r + 1 < np) ? pstart[r + 1] : n;
                    size_t ss = s;
                    int64_t last_ts = es[s].ts;
                    for (size_t i = s + 1; i <= e; i++) {
                        bool boundary = (i == e);
                        if (i < e) {
                            if (es[i].ts != last_ts) {
                                if (es[i].ts - last_ts > SESSION_GAP) boundary = true;
                                last_ts = es[i].ts;
                            }
                        }
                        if (boundary) {
                            if (ss < i) {
                                int64_t start = es[ss].ts;
                                Session sess{};
                                sess.person = (uint32_t)es[ss].user_id;
                                sess.day = (int32_t)(start / MS_PER_DAY - base_day);
                                sess.start = start;
                                for (size_t j = ss; j < i; j++) {
                                    sess.events++;
                                    if (es[j].type == 2) { sess.has_purchase = 1; sess.revenue += es[j].price; outp.push_back({(uint32_t)es[j].user_id, sess.day, es[j].category, es[j].price}); }
                                }
                                outs.push_back(sess);
                            }
                            ss = i;
                            if (i < e) last_ts = es[i].ts;
                        }
                    }
                }
            });
            size_t total_s = 0, total_p = 0;
            for (int t = 0; t < nt; t++) { total_s += psess[t].size(); total_p += ppurch[t].size(); }
            sessions.reserve(total_s); purchs.reserve(total_p);
            for (int t = 0; t < nt; t++) { sessions.insert(sessions.end(), psess[t].begin(), psess[t].end()); purchs.insert(purchs.end(), ppurch[t].begin(), ppurch[t].end()); }
        }
        es.clear(); es.shrink_to_fit();

        // ---------- clicks attribution ----------
        struct Ck { uint32_t person; int64_t ts; uint64_t cid; uint16_t campaign; };
        vector<Ck> cks(clicks.size());
        parallel_for(nt, clicks.size(), [&](int, size_t lo, size_t hi) {
            for (size_t i = lo; i < hi; i++) {
                const Click& c = clicks[i];
                cks[i] = {(uint32_t)c.user_id, c.ts, c.click_id, (uint16_t)c.campaign};
            }
        });
        clicks.clear(); clicks.shrink_to_fit();

        radix_sort(cks, [&](const Ck& c){ return ((uint64_t)c.person << 32) | (uint32_t)(c.ts - key_base); }, nt, npass_person);
        // stable sort by person, ts; within equal ts, cid desc via a second pass is not needed:
        // we do a stable radix sort by (person, ts) then a stable sort by cid desc? Use comparator via
        // two-level: re-sort equal (person,ts) groups by cid descending. Simpler: sort by cid desc globally after.
        // Actually attribution only needs, for each session, the latest click <= start; ties broken by smallest cid.
        // We replicate reference: sort by (person, ts asc, cid desc). Do it with a key trick:
        // key = person<<32 | ts_offset  (asc), then stable-sort by cid DESC within equal (person,ts).
        // We'll sort by cid desc first (stable), then by (person,ts) asc (stable) => (person,ts asc, cid desc).
        radix_sort(cks, [](const Ck& c){ return ~c.cid; }, nt); // cid desc (stable)
        radix_sort(cks, [&](const Ck& c){ return ((uint64_t)c.person << 32) | (uint32_t)(c.ts - key_base); }, nt, npass_person);

        const int NC = 2001, ND = 15;
        struct CampAgg { int64_t sessions=0, purchasing=0, revenue=0, assisted=0; };
        vector<CampAgg> camp(NC * ND);

        // sessions already sorted by (person, start) from parallel sessionize
        size_t ns = sessions.size(), nc = cks.size();
        // session person ranges
        vector<uint32_t> sperson; vector<size_t> sstart;
        { size_t i = 0; while (i < ns) { uint32_t p = sessions[i].person; size_t j = i; while (j < ns && sessions[j].person == p) j++; sperson.push_back(p); sstart.push_back(i); i = j; } }
        // click person ranges (dense person id -> [lo,hi))
        vector<size_t> ck_lo(P, 0), ck_hi(P, 0);
        { size_t i = 0; while (i < nc) { uint32_t p = cks[i].person; size_t j = i; while (j < nc && cks[j].person == p) j++; ck_lo[p] = i; ck_hi[p] = j; i = j; } }

        vector<vector<CampAgg>> local_camp(nt, vector<CampAgg>(NC * ND));
        parallel_for(nt, sperson.size(), [&](int tid, size_t lo, size_t hi) {
            auto& lc = local_camp[tid];
            vector<int32_t> mark(NC, -1);
            int32_t lsi = 0;
            for (size_t r = lo; r < hi; r++) {
                uint32_t p = sperson[r];
                size_t slo = sstart[r], shi = (r + 1 < sperson.size()) ? sstart[r + 1] : ns;
                size_t clo = ck_lo[p], chi = ck_hi[p];
                size_t lo2 = clo, hi2 = clo;
                for (size_t si = slo; si < shi; si++) {
                    const Session& s = sessions[si];
                    while (hi2 < chi && cks[hi2].ts <= s.start) hi2++;
                    while (lo2 < chi && cks[lo2].ts < s.start - CLICK_REACH) lo2++;
                    int credited = NC - 1;
                    if (lo2 < hi2 && cks[hi2-1].ts >= s.start - CLICK_REACH) credited = cks[hi2-1].campaign;
                    int d = s.day;
                    lc[credited * ND + d].sessions++;
                    if (s.has_purchase) lc[credited * ND + d].purchasing++;
                    lc[credited * ND + d].revenue += s.revenue;
                    for (size_t ci = lo2; ci < hi2; ci++) {
                        int cc = cks[ci].campaign;
                        if (mark[cc] != lsi) { mark[cc] = lsi; lc[cc * ND + d].assisted++; }
                    }
                    lsi++;
                }
            }
        });
        for (int t = 0; t < nt; t++)
            for (int i = 0; i < NC * ND; i++) {
                camp[i].sessions += local_camp[t][i].sessions;
                camp[i].purchasing += local_camp[t][i].purchasing;
                camp[i].revenue += local_camp[t][i].revenue;
                camp[i].assisted += local_camp[t][i].assisted;
            }

        // ---------- user_daily aggregation ----------
        // sessions sorted by (person, start); day is non-decreasing with start within a person
        struct UserAgg { uint32_t person; int32_t day; int64_t sessions, events, revenue; };
        vector<UserAgg> user_agg;
        for (auto& s : sessions) {
            if (!user_agg.empty() && user_agg.back().person == s.person && user_agg.back().day == s.day) {
                user_agg.back().sessions++; user_agg.back().events += s.events; user_agg.back().revenue += s.revenue;
            } else {
                user_agg.push_back({s.person, s.day, 1, (int64_t)s.events, s.revenue});
            }
        }
        sort(purchs.begin(), purchs.end(), [](const Purch& a, const Purch& b){
            if (a.person != b.person) return a.person < b.person;
            if (a.day != b.day) return a.day < b.day;
            return a.category < b.category;
        });
        static const char* cat_names[21] = {"apparel","automotive","baby","beauty","books","electronics","garden","grocery","home","jewelry","kitchen","music","office","outdoors","pets","shoes","sports","tools","toys","video_games","unknown"};
        int cat_rank[21];
        { vector<pair<string,int>> tmp; for (int i = 0; i < 21; i++) tmp.push_back({cat_names[i], i}); sort(tmp.begin(), tmp.end()); for (int i = 0; i < 21; i++) cat_rank[tmp[i].second] = i; }
        vector<int8_t> top_cat(user_agg.size(), -1);
        {
            size_t pi = 0;
            for (size_t ui = 0; ui < user_agg.size(); ui++) {
                int64_t best_rev = -1; int best_cat = -1;
                while (pi < purchs.size() && (purchs[pi].person < user_agg[ui].person || (purchs[pi].person == user_agg[ui].person && purchs[pi].day < user_agg[ui].day))) pi++;
                size_t pj = pi;
                while (pj < purchs.size() && purchs[pj].person == user_agg[ui].person && purchs[pj].day == user_agg[ui].day) {
                    uint8_t catidx = purchs[pj].category; int64_t rev = 0;
                    while (pj < purchs.size() && purchs[pj].person == user_agg[ui].person && purchs[pj].day == user_agg[ui].day && purchs[pj].category == catidx) { rev += purchs[pj].price; pj++; }
                    if (rev > best_rev || (rev == best_rev && cat_rank[catidx] < cat_rank[best_cat])) { best_rev = rev; best_cat = catidx; }
                }
                top_cat[ui] = (int8_t)best_cat;
            }
        }

        // ---------- write user_daily ----------
        {
            vector<ColSpec> cols(6);
            cols[0].name = "user_id"; cols[0].ptype = 6; cols[0].converted = 0;
            cols[1].name = "day"; cols[1].ptype = 1; cols[1].converted = 6;
            cols[2].name = "sessions"; cols[2].ptype = 2; cols[2].converted = -1;
            cols[3].name = "events"; cols[3].ptype = 2; cols[3].converted = -1;
            cols[4].name = "revenue_cents"; cols[4].ptype = 2; cols[4].converted = -1;
            cols[5].name = "top_category"; cols[5].ptype = 6; cols[5].converted = 0; cols[5].optional = true;
            // Build columns in parallel: per-thread buffers, concatenated in order.
            const size_t nua = user_agg.size();
            vector<array<vector<uint8_t>,5>> tdata(nt);
            vector<vector<uint8_t>> tcat(nt), tnull(nt);
            parallel_for(nt, nua, [&](int tid, size_t lo, size_t hi) {
                auto& d = tdata[tid];
                auto& c5 = tcat[tid];
                auto& n5 = tnull[tid];
                auto put_i32 = [](vector<uint8_t>& dd, int32_t v){ dd.push_back(v&0xFF); dd.push_back((v>>8)&0xFF); dd.push_back((v>>16)&0xFF); dd.push_back((v>>24)&0xFF); };
                auto put_i64 = [](vector<uint8_t>& dd, int64_t v){ for (int i=0;i<8;i++) dd.push_back((uint8_t)(v>>(8*i))); };
                auto put_bytes = [](vector<uint8_t>& dd, const char* s, size_t len){ int32_t L = (int32_t)len; dd.push_back(L&0xFF); dd.push_back((L>>8)&0xFF); dd.push_back((L>>16)&0xFF); dd.push_back((L>>24)&0xFF); dd.insert(dd.end(), s, s + len); };
                static const int cnlen[21] = {7,10,4,6,5,11,6,7,4,7,7,5,6,8,4,5,6,5,4,11,7};
                for (size_t ui = lo; ui < hi; ui++) {
                    auto& u = user_agg[ui];
                    const string& pn = person_name[u.person];
                    put_bytes(d[0], pn.data(), pn.size());
                    put_i32(d[1], (int32_t)(base_day + u.day));
                    put_i64(d[2], u.sessions);
                    put_i64(d[3], u.events);
                    put_i64(d[4], u.revenue);
                    int8_t tc = top_cat[ui];
                    if (tc >= 0) { put_bytes(c5, cat_names[tc], cnlen[tc]); n5.push_back(1); }
                    else { n5.push_back(0); }
                }
            });
            for (int t = 0; t < nt; t++) {
                for (int c = 0; c < 5; c++) cols[c].data.insert(cols[c].data.end(), tdata[t][c].begin(), tdata[t][c].end());
                cols[5].data.insert(cols[5].data.end(), tcat[t].begin(), tcat[t].end());
                cols[5].nulls.insert(cols[5].nulls.end(), tnull[t].begin(), tnull[t].end());
            }
            string dir = out + "/user_daily"; filesystem::create_directories(dir);
            write_parquet(dir + "/part-0.parquet", cols, (int64_t)user_agg.size());
        }

        // ---------- write campaign_daily ----------
        {
            vector<ColSpec> cols(7);
            cols[0].name = "campaign_id"; cols[0].ptype = 6; cols[0].converted = 0;
            cols[1].name = "channel"; cols[1].ptype = 6; cols[1].converted = 0;
            cols[2].name = "day"; cols[2].ptype = 1; cols[2].converted = 6;
            cols[3].name = "sessions"; cols[3].ptype = 2; cols[3].converted = -1;
            cols[4].name = "purchasing_sessions"; cols[4].ptype = 2; cols[4].converted = -1;
            cols[5].name = "revenue_cents"; cols[5].ptype = 2; cols[5].converted = -1;
            cols[6].name = "assisted_sessions"; cols[6].ptype = 2; cols[6].converted = -1;
            auto put_i32 = [](vector<uint8_t>& d, int32_t v){ d.push_back(v&0xFF); d.push_back((v>>8)&0xFF); d.push_back((v>>16)&0xFF); d.push_back((v>>24)&0xFF); };
            auto put_i64 = [](vector<uint8_t>& d, int64_t v){ for (int i=0;i<8;i++) d.push_back((uint8_t)(v>>(8*i))); };
            auto put_str = [&](vector<uint8_t>& d, const string& s){ put_i32(d, (int32_t)s.size()); d.insert(d.end(), s.begin(), s.end()); };
            static const char* chans[5] = {"affiliate","display","email","search","social"};
            int64_t nrows = 0;
            for (int c = 0; c < NC; c++) for (int d = 0; d < ND; d++) {
                auto& a = camp[c * ND + d];
                if (a.sessions == 0 && a.assisted == 0) continue;
                string cid = (c == NC - 1) ? "organic" : ("c_" + to_string(c + 1));
                string ch = (c == NC - 1) ? "organic" : chans[chan[c + 1]];
                put_str(cols[0].data, cid);
                put_str(cols[1].data, ch);
                put_i32(cols[2].data, (int32_t)(base_day + d));
                put_i64(cols[3].data, a.sessions);
                put_i64(cols[4].data, a.purchasing);
                put_i64(cols[5].data, a.revenue);
                put_i64(cols[6].data, a.assisted);
                nrows++;
            }
            string dir = out + "/campaign_daily"; filesystem::create_directories(dir);
            write_parquet(dir + "/part-0.parquet", cols, nrows);
        }
    }

    return 0;
}
