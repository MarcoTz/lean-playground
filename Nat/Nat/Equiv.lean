import Mathlib
import Nat.Base
import Nat.Mult
import Nat.Add

namespace MyNat

abbrev Nat.toNat (n:Nat): _root_.Nat := match n with 
  | Nat.zero => 0 
  | Nat.succ m => (Nat.toNat m) + 1 

abbrev Nat.fromNat (n:_root_.Nat): Nat := match n with 
  | 0 => zero
  | m + 1 => succ (Nat.fromNat m)

lemma Nat.zero_toNat: Nat.toNat (0:Nat) = 0 := rfl
lemma Nat.succ_toNat (n:Nat) : Nat.toNat (succ n) = (Nat.toNat n) + 1 := rfl


abbrev Nat.equivNat: Nat ≃ _root_.Nat where 
  toFun:= toNat
  invFun := fromNat
  left_inv n := by
    induction n 
    case zero => rfl
    case succ a ha => 
      unfold fromNat
      simp
      exact ha 
  right_inv n := by 
    induction n 
    case zero => rfl
    case succ a ha =>
      unfold toNat
      simp
      exact ha

abbrev Nat.map_add: ∀ (n m:Nat), Nat.toNat (n+m) = (Nat.toNat n) + (Nat.toNat m) := by 
  intro n m 
  induction n 
  case zero =>
    simp
    change Nat.toNat (m+0) = Nat.toNat m
    simp
  case succ a ha =>
    rw [Nat.succ_add]
    change (a+m).toNat + 1 = _ 
    change _ = a.toNat + 1 + m.toNat
    nth_rw 2 [_root_.Nat.add_comm]
    rw [ha]
    rw [← _root_.Nat.add_assoc]
    nth_rw 2 [_root_.Nat.add_comm]

abbrev Nat.add_map: ∀ (n m: _root_.Nat), Nat.fromNat n + Nat.fromNat m = Nat.fromNat (n+m) := by 
  intro n m 
  induction n
  case zero =>
    change 0 + fromNat m = _ 
    simp
  case succ n hn =>
    change succ (fromNat n) + fromNat m = _ 
    nth_rw 1 [_root_.Nat.add_comm,← _root_.Nat.add_assoc]
    change _ = succ (fromNat (m + n))
    rw [Nat.succ_add]
    rw [hn]
    rw [_root_.Nat.add_comm]


abbrev Nat.map_mul: ∀ (n m:Nat), (n*m).toNat = n.toNat * m.toNat := by 
  intro n m
  induction n 
  case zero => simp
  case succ n hn =>
    rw [Nat.succ_mul,Nat.map_add]
    change _ = (n.toNat + 1) * m.toNat
    rw [_root_.Nat.succ_mul]
    rw [hn]


lemma Nat.from_to: ∀ n:Nat, fromNat (toNat n) = n := by 
  intro n 
  induction n 
  case zero =>
    simp
  case succ a ha =>
    change fromNat (toNat a + 1) = _
    change succ (fromNat (toNat a)) = _ 
    rw [ha]

lemma Nat.to_from: ∀ n:_root_.Nat, toNat (fromNat n) = n := by 
  intro n
  induction n 
  case zero => simp
  case succ n hn =>
    change toNat (succ (fromNat n)) = _ 
    change toNat (fromNat n) + 1 = _ 
    rw [hn]

abbrev Nat.map_le_map_iff: ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by 
  intro n m
  constructor 
  case mp =>
    intro h
    apply _root_.Nat.exists_eq_add_of_le at h
    rcases h with ⟨k,hk⟩
    rw [Nat.le_iff]
    rw [← Nat.to_from k] at hk
    use (fromNat k)
    rw [← Nat.from_to m, ← Nat.from_to n]
    rw [hk]
    rw [Nat.to_from k]
    rw [Nat.add_map]
  case mpr => 
    intro h 
    rw [le_iff_exists_add]
    rw [Nat.le_iff]at h
    rcases h with ⟨c,hc⟩
    use c.toNat
    rw [← Nat.map_add,← hc]

lemma Nat.pow_eq_pow (n m:Nat) : n.toNat ^ m.toNat = (n^m).toNat := by 
  induction m
  case zero =>
    change (toNat n) ^ 0 = toNat (pow n 0)
    unfold pow 
    simp
  case succ m hm =>
    change (toNat n) ^ (toNat m + 1) = _
    rw [pow_succ,_root_.pow_succ,hm,Nat.map_mul]

abbrev Nat.equivNat_ordered_ring : Nat ≃+*o ℕ where
  toEquiv := Nat.equivNat
  map_add' := Nat.map_add
  map_mul' := Nat.map_mul
  map_le_map_iff' := Nat.map_le_map_iff


@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat 
  succ : Nat → Nat 
  succ_ne : ∀ n : Nat, succ n ≠ zero 
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m 
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n 

namespace PeanoAxioms
def Chapter2_Nat : PeanoAxioms where
  Nat := MyNat.Nat
  zero := MyNat.Nat.zero
  succ := MyNat.Nat.succ
  succ_ne := MyNat.Nat.succ_ne
  succ_cancel  := by
    intro n m 
    exact MyNat.Nat.succ_cancel n m 
  induction := MyNat.Nat.induction


def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := _root_.Nat.succ
  succ_ne := _root_.Nat.succ_ne_zero
  succ_cancel := _root_.Nat.succ_inj.mp
  induction _ := _root_.Nat.rec

abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | _root_.Nat.zero => P.zero
  | _root_.Nat.succ n => P.succ (natCast P n)

lemma natCastZero (P:PeanoAxioms): ∀ n:_root_.Nat, natCast P n = P.zero → n = 0 := by 
  intro n h
  unfold natCast at h 
  cases n
  case zero => rfl
  case succ n => 
    simp at h
    by_contra
    apply P.succ_ne at h 
    exact h

lemma natCastSucc (P:PeanoAxioms): 
    ∀ (n :_root_.Nat), natCast P (n+1) ≠ P.zero := by 
    intro n 
    cases n 
    case zero => 
      change P.succ P.zero  ≠ _ 
      apply P.succ_ne 
    case succ n => 
      change P.succ (P.natCast (n + 1)) ≠ _ 
      apply P.succ_ne

theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
  unfold Function.Injective 
  intro a₁ a₂ h
  induction a₁ generalizing a₂
  case zero =>
    change P.zero = _ at h
    symm at h
    apply natCastZero at h
    symm
    exact h
  case succ n hn => 
    cases a₂
    case zero =>
      by_contra
      apply natCastSucc at h 
      exact h
    case succ m =>
      change P.succ (P.natCast n) = P.succ (P.natCast m) at h
      apply P.succ_cancel at h
      apply hn at h
      simp
      exact h

theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective 
  apply P.induction 
  case _ => use 0 
  case _ => 
    intro n hn 
    rcases hn with ⟨a,ha⟩
    use (a+1)
    change P.succ (P.natCast a) = _
    rw [ha]


class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

lemma Peano.cancel_succ (P:PeanoAxioms) (n m:P.Nat): n = m → P.succ n  = P.succ m:= by 
  intro h 
  rw [h] 


abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    rw  [equiv.equiv_zero.symm]
    simp
  equiv_succ n := by
    revert n
    apply Q.induction
    case _ =>
      rw [← equiv.equiv_zero]
      rw [← equiv.equiv_succ]
      simp
    case _ =>
      intro n hn 
      rw [hn]
      have h := equiv.equiv.surjective
      rw [← Equiv.toFun_as_coe] at h
      unfold Function.Surjective at h 
      have h2:=h (Q.succ n)
      rcases h2 with ⟨a,ha⟩
      rw [← ha]
      simp
      rw [← equiv.equiv_succ]
      simp
      apply Peano.cancel_succ P
      have h2:= equiv.equiv.symm.surjective
      rw [← Equiv.toFun_as_coe] at h2 
      unfold Function.Surjective at h2 
      have h3:= h2 a
      rcases h3 with ⟨ b,hb⟩
      rw [← hb]
      simp 
      rw [← hn]
      simp
      rw [← ha,← hb]
      simp

abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    rw [← equiv2.equiv_zero]
    rw [← equiv1.equiv_zero] 
    simp
  equiv_succ n := by 
    unfold equiv
    simp
    change equiv2.equiv (equiv1.equiv (P.succ n)) =  _
    change _ = R.succ (equiv2.equiv (equiv1.equiv n))
    rw [equiv1.equiv_succ]
    rw [equiv2.equiv_succ]


end PeanoAxioms 

end MyNat
