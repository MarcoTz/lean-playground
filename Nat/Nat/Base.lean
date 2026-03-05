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

lemma Nat.zero_succ : Nat.succ Nat.zero = (1 : Nat) := by rfl
lemma Nat.one_succ: Nat.succ (1:Nat) = (2:Nat) := by rfl
lemma Nat.two_succ: Nat.succ (2:Nat) = (3:Nat) := by rfl

lemma Nat.succ_ne (n:Nat) : succ n ≠ (0:Nat) := by 
  by_contra h
  injection h

lemma Nat.four_ne: (4:Nat) ≠ 0 := by
  change succ 3 ≠ 0
  exact Nat.succ_ne _

theorem Nat.succ_cancel (n m:Nat) (hnm: succ n = succ m): n = m := by 
  injection hnm

theorem Nat.succ_ne_succ (n m:Nat): n≠m → succ n ≠ succ m := by
  intro h
  contrapose h
  apply succ_cancel at h 
  exact h

lemma Nat.self_ne_succ (n:Nat): n ≠ succ n:= by 
  induction n 
  case zero => 
    symm
    apply Nat.succ_ne
  case succ m hm => 
    apply Nat.succ_ne_succ
    exact hm
   

theorem Nat.six_ne_two: (6:Nat) ≠ 2 := by 
  by_contra h 
  change succ 5 = succ 1 at h
  apply succ_cancel at h 
  change succ 4 = succ 0 at h
  apply succ_cancel at h
  have := four_ne
  contradiction

theorem Nat.induction (P:Nat→Prop) (hbase: P 0) (hind: ∀ n,P n → P (succ n)): ∀ n, P n := by 
  intro n
  induction n with
    | zero => exact hbase
    | succ a _ => 
      apply hind
      tauto

abbrev Nat.recurse (f: Nat→Nat→Nat) (c:Nat): Nat→Nat := fun n ↦ match n with 
  | zero => c 
  | succ n => f n (recurse f c n)

theorem Nat.recurse_zero (f:Nat→Nat→Nat) (c:Nat) : 
    recurse f c 0  = c := by rfl

theorem Nat.recurse_succ (f:Nat→Nat→Nat) (c:Nat) (n:Nat):
     recurse f c (succ n) = f n (recurse f c n) := by rfl

theorem Nat.eq_recurse (f:Nat→Nat→Nat) (c:Nat) (a:Nat→Nat): 
    (a 0 = c ∧ ∀n, a (succ n) = f n (a n)) ↔ a = recurse f c := by 
  constructor 
  case mp  => 
    intro ⟨hl,hr⟩
    apply funext
    apply induction
    case h.hbase=>
      change a 0 = c
      exact hl
    case h.hind => 
    intro x h
    rw [hr]
    rw [h]
  case mpr => 
    intro h
    constructor
    case left => 
      rw [h]
    case right => 
    intro n
    rw [h]

theorem Nat.recurse_uniq (f:Nat→Nat→Nat) (c:Nat): 
    ∃! (a:Nat→Nat), a 0 = c ∧ ∀ n, a (succ n) = f n (a n) := by
      apply ExistsUnique.intro (recurse f c)
      case h₁ => 
        change c = c∧∀(n:Nat),recurse f c (succ n) = f n (recurse f c n)
        constructor
        case left=> rfl
        case right => 
        intro n 
        rfl
      case h₂ => 
        intro y ⟨hl,hr⟩
        apply funext
        intro x 
        induction x
        case zero =>
          change y 0 = c
          exact hl
        case succ a ha => 
          rw [hr]
          rw [ha]
        
end MyNat 
