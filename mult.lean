import Mathlib
import nat
import add

namespace MyNat

abbrev Nat.mul (n m: Nat): Nat := Nat.recurse (fun _ prod ↦  prod + m) 0 n 

instance Nat.isMul: Mul Nat where 
  mul := mul 

@[simp]
theorem Nat.zero_mul (m: Nat): 0 * m = 0 := recurse_zero (fun _ prod ↦ prod * m) _


theorem Nat.succ_mul (n m:Nat): (succ n) * m = n * m + m := by 
  change mul (succ n) m = mul n m + m 
  unfold mul 
  simp

@[simp]
lemma Nat.mul_zero (n : Nat): n * 0 = 0 := by 
  induction n 
  case zero =>
    change 0 * 0 = 0 
    rw [Nat.zero_mul]
  case succ n hn => 
    rw [Nat.succ_mul,hn,Nat.add_zero]



theorem Nat.one_mul (n:Nat): 1 * n = n := by 
  rw [← Nat.zero_succ]
  apply Nat.succ_mul

theorem Nat.two_mul (n:Nat): 2 * n = n + n := by 
  rw [← Nat.one_succ,Nat.succ_mul,Nat.one_mul]

lemma Nat.mul_one (n:Nat): n*1 = n := by
  induction n 
  case zero => 
    change 0 * 1 = 0
    rw [Nat.zero_mul]
  case succ n hn =>
    rw [Nat.succ_mul]
    rw [hn]
    rw [Nat.succ_eq_add_one]

lemma Nat.mul_succ (n m:Nat): n * (succ m) = n * m + n := by 
  induction n
  case zero =>
    change 0 * succ m  = 0 * m + 0 
    rw [Nat.add_zero,Nat.zero_mul,Nat.zero_mul]
  case succ n hn =>
    rw [Nat.succ_mul,hn,Nat.succ_mul,Nat.add_succ,Nat.add_succ]
    simp 
    nth_rw 2 [← Nat.add_assoc]
    nth_rw 3 [Nat.add_comm]
    rw [← Nat.add_assoc]
    nth_rw 1 [Nat.add_comm]
    nth_rw 2 [Nat.add_comm]

theorem Nat.mul_comm (n m:Nat): n * m = m * n := by 
  induction n 
  case zero =>
    change 0 * m = m * 0
    rw [Nat.zero_mul,Nat.mul_zero]
  case succ n hn =>
    rw [Nat.mul_succ,Nat.succ_mul,hn]

lemma Nat.pos_mul_pos {n m: Nat} (h₁:n.isPos) (h₂:m.isPos): (n*m).isPos := by 
  induction n
  case zero =>
    unfold isPos at h₁
    change 0 ≠ 0 at h₁ 
    contradiction
  case succ a ha =>
      rw [Nat.succ_mul]
      apply add_pos_right
      exact h₂

lemma Nat.mul_eq_zero (n m:Nat): n*m = 0 ↔ n = 0 ∨ m = 0 := by 
  constructor 
  case mp => 
    intro h 
    induction n 
    case zero =>
      left 
      change 0 = 0 
      rfl
    case succ n hn =>
      rw [Nat.succ_mul] at h 
      apply Nat.add_eq_zero at h 
      rcases h with ⟨_,hm⟩
      right 
      exact hm 
  case mpr =>
    intro h
    rcases h 
    case inl h => 
      rw [h]
      apply Nat.zero_mul
    case inr h =>
      rw [h]
      apply Nat.mul_zero

@[simp]
theorem Nat.mul_add (a b c:Nat): a * (b+c) = a*b + a*c := by 
  induction c 
  case zero =>
    change a * (b+0) = a*b + a * 0
    rw [Nat.add_zero,Nat.mul_zero,Nat.add_zero]
  case succ c hc =>
    rw [Nat.add_succ,Nat.mul_succ,Nat.mul_succ,hc,← Nat.add_assoc]

@[simp]
theorem Nat.add_mul (a b c:Nat): (a + b)*c = a*c + b*c := by
    rw [Nat.mul_comm]
    nth_rw 2 [Nat.mul_comm]
    nth_rw 3 [Nat.mul_comm]
    exact Nat.mul_add c a b

theorem Nat.mul_assoc (a b c:Nat): (a*b)*c = a * (b*c) := by 
  induction a
  case zero =>
    change 0 * b * c = 0 * (b*c)
    repeat rw [Nat.zero_mul]
  case succ a ha =>
    rw [Nat.succ_mul,Nat.succ_mul,Nat.add_mul,ha]

instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring

theorem Nat.mul_lt_mul_of_pos_right { a b c:Nat } (h: a < b) (hc:c.isPos): 
    a * c < b * c := by 
    rw [Nat.lt_iff]
    constructor 
    case left =>
      unfold isPos at hc 
      have hc2: c > 0 := by 
        cases c 
        case zero =>
          change 0 ≠ 0 at hc 
          contradiction
        case succ c =>
          apply Nat.succ_gt_zero
      rw [Nat.lt_iff] at h
      rcases h with ⟨hl,hr⟩
      rcases hl with ⟨d,hd⟩
      rw [hd,Nat.add_mul]
      use d * c 
    case right =>
      rw [Nat.lt_iff] at h 
      rcases h with ⟨hl,hr⟩
      rcases hl with ⟨d,hd⟩
      rw [hd,Nat.add_mul]
      nth_rw 1 [← Nat.add_zero (a*c)]
      by_contra h
      apply Nat.add_left_cancel at h
      symm at h 
      rw [Nat.mul_eq_zero] at h 
      cases h 
      case inl h =>
        rw [h] at hd 
        rw [Nat.add_zero] at hd 
        symm at hd 
        contradiction
      case inr h =>
        unfold isPos at hc 
        contradiction
  
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.isPos): 
      a * c > b * c := mul_lt_mul_of_pos_right h hc 

theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h:a<b) (hc:c.isPos):
    c * a < c * b := by 
    simp [Nat.mul_comm] 
    exact Nat.mul_lt_mul_of_pos_right h hc

theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h:a>b) (hc:c.isPos):
    c * a > c * b := by
      simp [Nat.mul_comm]
      exact Nat.mul_gt_mul_of_pos_right h hc

lemma Nat.mul_cancel_right {a b c:Nat} (h:a*c = b*c) (hc:c.isPos): a = b := by 
  have ht:= Nat.trichotomous a b 
  cases ht 
  case inl hl =>
    rw [Nat.lt_iff] at hl 
    rcases hl with ⟨hl,hr⟩
    rcases hl with ⟨d,hd⟩
    rw [hd,Nat.add_mul] at h 
    nth_rw 1 [← Nat.add_zero (a*c)] at h 
    apply Nat.add_left_cancel at h
    symm at h 
    rw [Nat.mul_eq_zero] at h
    cases h 
    case inl hl => 
      by_contra
      rw [hl,Nat.add_zero] at hd 
      symm at hd 
      contradiction
    case inr hc2 => 
      by_contra
      unfold isPos at hc
      contradiction
  case inr hr =>
    cases hr 
    case inl hrl => exact hrl 
    case inr hrr => 
      rw [Nat.gt_iff_lt,Nat.lt_iff] at hrr
      rcases hrr with ⟨hrl,hrr⟩
      rcases hrl with ⟨d,hd⟩
      rw [hd,Nat.add_mul] at h 
      nth_rw 2 [← Nat.add_zero (b*c)] at h 
      apply Nat.add_left_cancel at h 
      rw [Nat.mul_eq_zero] at h 
      cases h 
      case inl hl => 
        rw [hl,Nat.add_zero] at hd
        symm at hrr 
        contradiction
      case inr hr =>
        unfold isPos at hc 
        contradiction

instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by
    rw [Nat.le_iff]
    use 1 
    rw [Nat.zero_add]
  mul_le_mul_of_nonneg_left := by 
    intro a ha b c hbc
    rw [Nat.le_iff_lt_or_eq] at ha 
    rw [Nat.le_iff_lt_or_eq] at hbc
    cases ha
    case inl hl =>
      cases hbc
      case inl hbcl =>
        rw [Nat.le_iff_lt_or_eq]
        left
        have ha: a.isPos := by 
          unfold isPos
          rw [Nat.lt_iff] at hl 
          rcases hl with ⟨_,hr⟩
          symm 
          exact hr 
        exact Nat.mul_lt_mul_of_pos_left hbcl ha 
      case inr hbcr =>
        rw [hbcr]
    case inr hr =>
      rw [← hr]
      rw [Nat.zero_mul,Nat.zero_mul,Nat.le_iff_lt_or_eq]
      right 
      rfl

  mul_le_mul_of_nonneg_right := by 
    intro c hc a b hab 
    rw [Nat.le_iff_lt_or_eq] at hab
    rw [Nat.le_iff_lt_or_eq] at hc 
    rw [Nat.le_iff_lt_or_eq]
    cases hc 
    case inl hl => 
      have hc: c.isPos := by
        unfold isPos
        rw [Nat.lt_iff] at hl 
        rcases hl with ⟨_,hr⟩
        symm at hr 
        exact hr 
      cases hab 
      case inl hl2 =>
        left 
        exact Nat.mul_lt_mul_of_pos_right hl2 hc 
      case inr hr =>
        rw [hr]
        right 
        rfl
    case inr hr =>
      right
      rw [← hr,Nat.mul_zero,Nat.mul_zero]

example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  case ha =>
    rw [Nat.le_iff]
    use d 
    rw [Nat.zero_add]
  case hbc.ha=>
    rw [Nat.le_iff]
    use c 
    rw [Nat.zero_add]


theorem Nat.exists_div_mod (n:Nat) {q:Nat} (hq: q.isPos):
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by 
      induction n 
      case zero =>
        use 0,0
        simp
        constructor 
        case left =>
          rw [Nat.lt_iff]
          constructor 
          case left => use q; simp
          case right => unfold isPos at hq; symm; exact hq
        case right =>
          change 0=0
          rfl
      case succ n hn =>
        rcases hn with ⟨m,r,hr,hrq,hn⟩
        have h_tri:=trichotomous q (succ r)
        cases h_tri
        case inl h =>
          by_contra
          apply Nat.lt_squeeze r q hrq h
        case inr h =>
          cases h 
          case inl h =>
            use (succ m),0
            simp
            constructor 
            case left =>
              rw [Nat.lt_iff]
              constructor 
              case left => use q; simp
              case right => unfold isPos at hq; symm; exact hq
            case right =>
              rw [hn,← Nat.add_succ,Nat.succ_mul]
              nth_rw 3 [h]
          case inr h =>
            use m,(succ r)
            constructor 
            case left =>
              apply Nat.zero_le
            case right =>
              constructor 
              case left =>
                rw [Nat.gt_iff_lt] at h
                exact h 
              case right =>
                rw [hn,← Nat.add_succ]

abbrev Nat.pow (m n:Nat): Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

@[simp]
theorem Nat.pow_zero (m:Nat): m ^ 0 = 1 := recurse_zero (fun _ prod↦ prod*m) _

@[simp]
theorem Nat.pow_succ (m n:Nat): (m:Nat)^(succ n) = m^n*m := by 
  induction n
  case zero =>
    change Nat.pow m (succ 0) = m ^ 0 * m
    unfold pow 
    apply recurse_succ
  case succ n hn => 
    rw [hn]
    apply recurse_succ

@[simp]
theorem Nat.pow_one (m:Nat): m^1 = m := by 
  change pow m 1 = m 
  rw [← Nat.zero_succ]
  apply recurse_succ

lemma Nat.pow_two (n:Nat): n^2 = n*n := by 
  change pow n (succ 1) = _
  apply Nat.recurse_succ


theorem Nat.sq_add_eq (a b:Nat): 
    (a + b)^2 = a^2 + 2 * a * b + b^2 := by 
  repeat rw [Nat.pow_two]
  simp
  repeat rw [← Nat.add_assoc]
  grind [Nat.add_comm]

end MyNat
