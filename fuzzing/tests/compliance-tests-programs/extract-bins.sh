#!/bin/sh 

set -e

SCRIPT_ROOT=$(dirname "$0")
OBJCOPY=riscv64-elf-objcopy

echo Script root: $SCRIPT_ROOT

for elf in "$SCRIPT_ROOT"/*.elf; do 
  name=$(basename $elf .elf)
  bin=$name.bin 
  text=$name.text

  $OBJCOPY -O binary $elf $bin
  $OBJCOPY -O binary --only-section=.text $elf $text
  echo Extracted $name
done
