module

/-! Code that cannot be linked into a native library. -/

/-- An external function that no library defines. -/
@[extern "devNativeTest_missing"]
public opaque missing : Nat → Nat

public def useMissing (n : Nat) : Nat := missing n + 1
