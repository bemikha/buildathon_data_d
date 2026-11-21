# Shopping Sessions: single-pass C++17 pipeline (no runtime deps).
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends g++ \
    && rm -rf /var/lib/apt/lists/*

# The scorer runs the container as uid 1000; give that uid a name and a home.
RUN useradd --uid 1000 --no-create-home --home-dir /scratch app

COPY pipeline.cpp /app/pipeline.cpp
RUN g++ -O3 -march=x86-64-v4 -std=c++17 -pthread -o /app/pipeline /app/pipeline.cpp \
    && rm /app/pipeline.cpp

COPY run.sh /app/run.sh
RUN chmod +x /app/run.sh

WORKDIR /app
CMD ["/app/run.sh"]
