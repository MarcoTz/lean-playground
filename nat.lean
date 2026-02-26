import Mathlib
namespace MyNat 


inductive Nat where 
 | zero : Nat
 | succ : Nat -> Nat
deriving Repr, DecidableEq

instance Nat.zeroNat: Zero Nat :=  ⟨zero⟩
#check (0:Nat)

instance Nat.succNat { n: _root_.Nat } : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦  succ n) n
#check (fun n ↦  Nat.succ n)

instance Nat.oneNat: One Nat := ⟨1⟩

theorem Nat.zero_succ : Nat.succ Nat.zero = (1 : Nat) := by rfl

end MyNat 

