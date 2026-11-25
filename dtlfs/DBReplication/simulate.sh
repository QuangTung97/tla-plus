#!/bin/bash
set -euo pipefail

SEARCH_DIR="$HOME/.vscode/extensions"
EXTENSION_PATH=("$SEARCH_DIR/tlaplus.vscode-ide-"*)
TOOL_PATH="$EXTENSION_PATH/tools/tla2tools.jar"

MODEL_NAME=DBReplication

OPTIONS="num=10"
OPTIONS=""

set -x

java \
    -Xmx12g \
    -cp "$TOOL_PATH" \
    -XX:+UseParallelGC \
    -DTLA-Library= tlc2.TLC $MODEL_NAME.tla \
    -tool -simulate $OPTIONS -seed 123456789 \
    -config $MODEL_NAME.cfg \
    -workers 10
