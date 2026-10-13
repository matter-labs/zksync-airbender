import Image

/-- Writes `Image.bytes` to stdout; verify.sh compares it with build/app.bin. -/
def main : IO Unit := do
  (← IO.getStdout).write (ByteArray.mk (Image.bytes.map (·.toNat.toUInt8)))
