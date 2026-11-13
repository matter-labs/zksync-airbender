#!/bin/sh

cargo objdump --release -Z build-std=core,alloc -v -- -d