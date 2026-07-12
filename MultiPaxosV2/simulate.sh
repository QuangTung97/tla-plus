#!/bin/bash
set -euo pipefail

java \
    -Xmx12g \
    -cp /home/quangtung/.vscode/extensions/tlaplus.vscode-ide-2026.6.242335/tools/tla2tools.jar \
    -XX:+UseParallelGC \
    -DTLA-Library= tlc2.TLC MultiPaxosV2.tla \
    -tool -simulate num=1000 -seed 123456789 \
    -config /home/quangtung/tla-plus/MultiPaxosV2/MultiPaxosV2.cfg \
    -workers 2
