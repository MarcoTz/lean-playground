import Nat.Base

namespace MyNat
/-set_option trace.Meta.synthInstance true-/

abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ succ sum) m n

instance Nat.instAdd : Add Nat where 
  add := add

@[simp]
theorem Nat.zero_add (m:Nat): 0 + m = m := by
  apply recurse_zero (fun _ sum ↦ succ sum) _

@[simp]
theorem Nat.succ_add (n m: Nat):  succ n + m  = succ (n+m) := by rfl

theorem Nat.one_add (m:Nat): 1+m = succ m := by 
  apply succ_add

theorem Nat.two_add (m:Nat): 2+m = succ (succ m) := by 
  apply one_add


example: (2:Nat) + 3 = 5 := by
  apply Nat.two_add

@[simp]
lemma Nat.add_zero (m:Nat): m+0 = m := by 
  induction m
  case zero => 
    apply Nat.zero_add
  case succ a ha => 
    rw [Nat.succ_add]
    rw [ha]

@[simp]
lemma Nat.add_succ (n m: Nat): n + succ m = succ (n+m) := by 
  induction n 
  case zero => 
    change 0 + (succ m) = succ (0 + m)
    repeat rw [Nat.zero_add]
  case succ a ha => 
    rw [succ_add,ha,succ_add]
    
lemma Nat.succ_eq_add_one (n: Nat): n + 1 = succ n := by 
  change n + succ 0 = succ n
  rw [Nat.add_succ, Nat.add_zero]

@[simp]
theorem Nat.add_comm (n m : Nat):  n + m = m + n := by 
  induction n 
  case zero => 
    change 0 + m = m + 0
    rw [Nat.zero_add,Nat.add_zero]
  case succ a ha => 
    rw [Nat.succ_add,Nat.add_succ,ha]

@[simp]
theorem Nat.add_assoc (a b c: Nat): (a + b) + c = a + (b + c) := by 
  induction a
  case zero => 
    change 0 + b + c = 0 + (b+c)
    rw [Nat.zero_add,Nat.zero_add]
  case succ a ha => 
    repeat rw [Nat.succ_add]
    rw [ha]

theorem Nat.add_left_cancel (a b c: Nat) (habc: a + b = a + c): b = c := by
  induction a
  case zero => 
    change 0 + b = 0 + c at habc
    repeat rw [Nat.zero_add] at habc
    exact habc
  case succ a ha => 
    apply ha 
    repeat rw [Nat.succ_add] at habc
    apply Nat.succ_cancel at habc
    exact habc

lemma Nat.add_cancel_left (a b c:Nat) (hbc: b = c): a + b = a + c := by 
  induction a 
  case zero => 
    change 0 + b = 0 + c 
    rw [Nat.zero_add,Nat.zero_add]
    exact hbc 
  case succ d hd =>
    rw [Nat.succ_add,Nat.succ_add]
    rw [hd]



theorem Nat.add_right_cancel (a b c: Nat) (habc: b + a = c + a): b = c := by 
  rw [Nat.add_comm] at habc
  nth_rewrite 2 [Nat.add_comm] at habc
  revert habc
  apply Nat.add_left_cancel a b c   

lemma Nat.add_cancel_right (a b c:Nat) (hbc: b = c): b + a = c + a := by 
  rw [hbc]

example (a b c d:Nat): (a+b)+(c+0+d) = (b+c)+(d+a) := by
  rw [Nat.add_zero]
  nth_rewrite 2 [← Nat.add_assoc]
  nth_rewrite 4 [Nat.add_comm]
  repeat rw [← Nat.add_assoc]

def Nat.isPos (n:Nat):Prop:= n≠ 0

lemma Nat.isPos_iff (n:Nat): n.isPos ↔ n ≠ 0 := by rfl 

theorem add_pos_left (a b: Nat) (ha: a.isPos): (a+b).isPos := by 
  induction b
  case zero => 
    change (a + 0).isPos
    rw [Nat.add_zero]
    exact ha
  case succ c hc => 
    rw [Nat.add_succ]
    apply Nat.succ_ne

theorem add_pos_right (a b:Nat) (hb: b.isPos): (a+b).isPos:= by
  rw [Nat.add_comm]
  apply add_pos_left
  exact hb

theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0): a = 0 ∧ b = 0 := by
  constructor
  case left => 
    induction a
    case zero => rfl
    case succ c hc => 
    rw [Nat.succ_add] at hab 
    contradiction
  case right => 
    induction b
    case zero => rfl
    case succ c hc => 
      rw [Nat.add_succ] at hab 
      contradiction

lemma Nat.uniq_succ_eq (a:Nat) (ha:a.isPos): ∃! b, succ b = a := by 
  induction a
  case zero => 
    rw [Nat.isPos_iff] at ha
    contradiction
  case succ c hc => 
    apply ExistsUnique.intro c
    case h₁ => 
      rfl
    case h₂ => 
      intro y 
      apply Nat.succ_cancel

instance Nat.instLE: LE Nat where 
  le n m := ∃ a : Nat, m = n + a

instance Nat.instLT: LT Nat where 
  lt n m := n ≤ m ∧ n ≠ m  

lemma Nat.le_iff (n m: Nat): n ≤ m ↔ ∃ a:Nat, m = n+a:= by rfl

lemma Nat.lt_iff (n m: Nat): n < m ↔ (∃ a:Nat, m = n+a) ∧ n≠m := by rfl

lemma Nat.ge_iff_le (n m:Nat): n ≥ m ↔ m ≤ n := by rfl 

lemma Nat.gt_iff_lt (n m: Nat): n > m ↔ m < n := by rfl

lemma Nat.le_of_lt (n m:Nat) (hnm : n < m ) : n ≤ m := by 
  rw [Nat.lt_iff] at hnm
  cases hnm with
    | intro hl hr => 
    rw [Nat.le_iff]
    exact hl

lemma Nat.ge_of_gt (n m:Nat) (hnm: n > m): n ≥ m:= by 
  rw [Nat.ge_iff_le]
  rw [Nat.gt_iff_lt] at hnm
  apply Nat.le_of_lt
  exact hnm


lemma Nat.le_iff_lt_or_eq (n m : Nat): (n ≤ m) ↔ (n < m) ∨ n = m := by 
  constructor
  case mp => 
    intro h
    rw [Nat.le_iff] at h
    rw [Nat.lt_iff]  
    rcases h with ⟨k,hk⟩
    cases k
    case zero => 
      right
      change m = n + 0 at hk 
      rw [Nat.add_zero] at hk 
      symm
      exact hk
    case succ i => 
      left
      constructor
      case left => 
        use succ i
      case right =>
        rw [Nat.add_succ] at hk
        rw [hk]
        by_contra hn
        rw [← succ_eq_add_one] at hn
        rw [Nat.add_assoc] at hn 
        rw [← Nat.add_zero n] at hn
        nth_rewrite 2 [Nat.add_zero n] at hn
        apply Nat.add_left_cancel n 0 (i+1) at hn
        rw [succ_eq_add_one] at hn
        symm at hn
        apply Nat.succ_ne at hn
        contradiction          
  case mpr => 
    intro h 
    cases h
    case inl hl => 
      apply Nat.le_of_lt
      exact hl
    case inr hr =>
      rw [Nat.le_iff]
      use zero
      case h => 
        change m = n + 0 
        rw [Nat.add_zero]
        symm
        exact hr
  
example: (8:Nat) > 5 := by 
 rw [Nat.gt_iff_lt,Nat.lt_iff]
 constructor
 case left => 
  use 3 
  rfl
 case right => 
  by_contra
  contradiction

theorem Nat.succ_gt_self (n:Nat): succ n > n := by
  rw [Nat.gt_iff_lt,Nat.lt_iff]
  constructor
  case left => 
    use 1
    rw [← succ_eq_add_one]
  case right => 
    rw [← succ_eq_add_one]
    nth_rewrite 1 [← Nat.add_zero n] 
    by_contra h
    apply Nat.add_left_cancel n 0 1 at h
    contradiction


theorem Nat.ge_refl (a:Nat): a ≥ a := by 
  rw [Nat.ge_iff_le,Nat.le_iff]
  use 0
  rw [Nat.add_zero]

theorem Nat.le_refl (a:Nat): a ≤ a := by 
  rw [← Nat.ge_iff_le]
  apply Nat.ge_refl

example (a b : Nat): a + b ≥ a + b := by apply Nat.ge_refl

theorem Nat.ge_trans (a b c : Nat) (hab: a ≥ b) (hbc: b ≥ c): a ≥ c := by 
   rw [Nat.ge_iff_le] at hab hbc
   rw [Nat.ge_iff_le] 
   rw [Nat.le_iff] at hab hbc
   rw [Nat.le_iff]
   rcases hab with ⟨ d, hd ⟩
   rcases hbc with ⟨ e,he ⟩
   use d+e
   rw [hd,he]
   nth_rewrite 4 [Nat.add_comm]
   rw [← Nat.add_assoc]


theorem Nat.le_trans (a b c: Nat) (hab: a ≤ b) (hbc: b ≤ c): a ≤ c := by 
  rw [← Nat.ge_iff_le] at hab hbc
  rw [← Nat.ge_iff_le]
  apply Nat.ge_trans c b a 
  case hab => exact hbc
  case hbc => exact hab

theorem Nat.lt_trans (a b c:Nat) (hab: a < b) (hbc: b < c): a < c := by 
  rw [Nat.lt_iff]
  rw [Nat.lt_iff] at hab hbc
  rcases hab with ⟨habl,habr⟩
  rcases hbc with ⟨hbcl,hbcr⟩
  rcases habl with ⟨w,hw⟩
  rcases hbcl with ⟨v,hv⟩
  constructor 
  case left =>
    rw [hv,hw]
    use w + v
    rw [Nat.add_assoc]
  case right => 
    by_contra h
    rw [h] at hw 
    rw [hv] at hw 
    nth_rewrite 1 [← Nat.add_zero b] at hw 
    have h1: v + w = 0 := by 
      apply Nat.add_left_cancel b
      symm
      rw [← Nat.add_assoc]
      exact hw 
    have h2: v = 0 ∧ w = 0 := by 
      apply Nat.add_eq_zero
      exact h1 
    rcases h2 with ⟨v0,w0⟩
    rw [v0] at hv
    rw [Nat.add_zero] at hv 
    symm at hv 
    contradiction


theorem Nat.gt_trans (a b c:Nat) (hab: a > b) (hbc: b > c) : a > c := by 
  rw [Nat.gt_iff_lt]
  rw [Nat.gt_iff_lt] at hab hbc
  apply Nat.lt_trans c b a
  case hab => exact hbc 
  case hbc => exact hab 

lemma Nat.succ_gt_zero (n:Nat): succ n > 0 := by 
  induction n 
  case zero => 
    change succ 0 > 0 
    apply Nat.succ_gt_self
  case succ m hm =>
    apply Nat.gt_trans (succ (succ m)) (succ m) 0 
    case hab => 
      rw [Nat.gt_iff_lt,  Nat.lt_iff]
      constructor 
      case left => 
        use 1 
        rw [Nat.succ_eq_add_one]
      case right => 
        by_contra h
        apply Nat.succ_cancel at h
        apply Nat.self_ne_succ at h 
        contradiction
    exact hm




theorem Nat.ge_antisymm (a b : Nat) (hab: a ≥ b) (hba : b ≥ a): a = b := by 
  rcases hab with ⟨c, hc⟩
  rw [hc]
  cases c 
  case zero =>
    change b + 0 = b 
    rw [Nat.add_zero]
  case succ d =>
    rw [hc] at hba
    by_contra
    rw [ge_iff_le] at hba
    rw [le_iff] at hba
    rcases hba with ⟨w,hw⟩
    nth_rewrite 1 [← Nat.add_zero b] at hw 
    rw [Nat.add_assoc] at hw 
    apply Nat.add_left_cancel b 0 (succ d + w) at hw 
    rw [Nat.succ_add] at hw 
    have h: succ (d+w) ≠ 0 := Nat.succ_ne (d + w)
    contradiction


theorem Nat.add_ge_add_right ( a b c: Nat): a ≥ b ↔ a + c ≥ b + c := by
    constructor
    case mp => 
      intro ha 
      rcases ha with ⟨d,hd⟩
      rw [Nat.ge_iff_le,le_iff]
      use d
      rw [hd]
      rw [Nat.add_assoc]
      nth_rw 2 [Nat.add_comm]
      rw [← Nat.add_assoc]
    case mpr => 
      intro h
      rw [Nat.ge_iff_le,Nat.le_iff] at h
      rw [Nat.ge_iff_le,Nat.le_iff]
      rcases h with ⟨d,hd⟩
      use d
      nth_rewrite 2 [Nat.add_comm] at hd
      rw [← Nat.add_assoc] at hd 
      have h: a = d + b := by 
        apply Nat.add_right_cancel c a (d + b) 
        exact hd
      rw [Nat.add_comm] at h
      exact h

theorem Nat.add_ge_add_left (a b c: Nat): a ≥ b ↔ c + a ≥ c + b := by
    rw [Nat.add_comm]
    nth_rewrite 2 [Nat.add_comm]
    revert a b c
    exact Nat.add_ge_add_right

theorem Nat.add_le_add_right (a b c: Nat): a ≤ b ↔ c + a ≤ c + b := by 
  repeat rw [← Nat.ge_iff_le]
  apply Nat.add_ge_add_left

theorem Nat.add_lt_add_right (a b c: Nat): a < b ↔ c + a < c + b := by 
  constructor 
  case mp => 
    intro h 
    rcases h with ⟨ hl,hr⟩
    rw [Nat.lt_iff]
    constructor 
    case left => 
      rcases hl with ⟨ w, hw⟩
      use w
      rw [hw]
      rw [Nat.add_assoc]
    case right => 
      by_contra h
      apply Nat.add_left_cancel at h
      contradiction
  case mpr => 
    intro h
    rcases h with ⟨ hl,hr⟩
    rw [Nat.lt_iff]
    constructor 
    case left => 
      rcases hl with ⟨ w, hw⟩
      use w
      apply Nat.add_left_cancel c
      rw [← Nat.add_assoc]
      exact hw 
    case right => 
      by_contra h 
      have h2: c + a = c + b := by 
        rw [h]
      contradiction

theorem Nat.add_lt_add_left (a b c:Nat): a < b ↔ a + c < b + c := by 
  nth_rw 1 [Nat.add_comm]
  nth_rw 2 [Nat.add_comm]
  apply Nat.add_lt_add_right

theorem Nat.add_gt_add_right  (a b c: Nat): a > b ↔ c + a > c + b := by
  rw [Nat.gt_iff_lt]
  rw [Nat.gt_iff_lt]
  rw [← Nat.add_lt_add_right b a c ]
 

theorem Nat.add_le_add_left (a b c: Nat): a ≤ b ↔ a + c ≤ b + c := by 
  repeat rw [← Nat.ge_iff_le]
  apply Nat.add_ge_add_right

theorem Nat.lt_iff_succ_le (a b: Nat): a < b ↔ succ a ≤ b := by 
  constructor 
  case mp => 
    intro h 
    rw [Nat.le_iff]
    rw [Nat.lt_iff] at h 
    rcases h with ⟨ hl, hr ⟩ 
    rcases hl with ⟨ c, hc⟩
    rw [hc]
    cases c 
    case zero => 
      by_contra
      change b = a + 0 at hc 
      rw [Nat.add_zero] at hc 
      symm at hc 
      contradiction
    case succ d => 
      use d 
      rw [Nat.add_succ]
      rw [Nat.succ_add]
  case mpr => 
    intro h 
    rcases h with ⟨ w, hw ⟩
    rw [hw]
    cases w 
    case zero =>
      change a < succ a + 0 
      rw [Nat.add_zero,← Nat.gt_iff_lt]
      apply Nat.succ_gt_self
    case succ v => 
      apply Nat.lt_trans a (succ a) (succ a + succ v)
      case hab => 
        rw [← Nat.gt_iff_lt]
        apply Nat.succ_gt_self
      case hbc=> 
        nth_rw 1 [← Nat.add_zero (succ a)]
        rw [ ← Nat.add_lt_add_right 0 (succ v) (succ a)]
        rw [← Nat.gt_iff_lt]
        apply Nat.succ_gt_zero

theorem Nat.lt_iff_add_pos (a b:Nat): a<b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by 
  constructor
  case mp => 
    intro h
    rw [Nat.lt_iff] at h
    rcases h with ⟨hl,hr⟩
    rcases hl with ⟨c,hc⟩
    use c
    constructor
    case left =>
      rw [Nat.isPos_iff]
      by_contra h
      rw [h,Nat.add_zero] at hc 
      symm at hc 
      contradiction
    case right =>
      exact hc
  case mpr => 
    intro h
    rcases h with ⟨d,hd⟩
    rcases hd with ⟨dpos,hb⟩
    rw [hb]
    cases d
    case zero => 
      rw [Nat.isPos_iff] at dpos
      change 0 ≠ 0 at dpos 
      by_contra
      contradiction
    case succ e =>
      nth_rw 1 [← Nat.add_zero a] 
      rw [← Nat.add_lt_add_right 0 (succ e) a]
      rw [← Nat.gt_iff_lt]
      apply Nat.succ_gt_zero

theorem ne_of_lt (a b :Nat): a < b → a ≠ b := by 
  intro h 
  rw [Nat.lt_iff] at h 
  rcases h with ⟨ hl,hr⟩
  exact hr 

theorem Nat.ne_of_gt (a b: Nat): a > b → a ≠ b := by 
  intro h
  rw [Nat.gt_iff_lt] at h
  symm
  revert h
  apply ne_of_lt b a

theorem Nat.not_lt_of_gt (a b :Nat): a < b ∧ a > b → False := by 
  intro h 
  rcases h with ⟨ hl, hr ⟩
  rw [Nat.lt_iff] at hl
  rw [Nat.gt_iff_lt,Nat.lt_iff] at hr 
  rcases hl with ⟨hlex,hlneq⟩
  rcases hr with ⟨hrex,hrneq⟩
  symm at hrneq
  rcases hlex with ⟨ c,hc⟩
  rcases hrex with ⟨d,hd⟩
  rw [hc] at hd 
  nth_rw 1 [← Nat.add_zero a] at hd
  have h:c + d = 0 := by
    symm
    apply Nat.add_left_cancel a 0 (c+d)
    rw [← Nat.add_assoc]
    exact hd
  rw [Nat.add_zero] at hd
  rw [hd,Nat.add_assoc] at hc
  nth_rw 3 [Nat.add_comm] at hc 
  rw [h,Nat.add_zero] at hc 
  have hcd : c=0 ∧ d = 0:= by 
    apply Nat.add_eq_zero
    exact h 
  rcases hcd with ⟨ hc0,hd0⟩
  rw [hc0,Nat.add_zero] at hc 
  symm at hc 
  contradiction

theorem Nat.not_lt_self (a:Nat) (h:a<a): False := by 
  rw [Nat.lt_iff] at h
  rcases h with ⟨ _, h⟩
  contradiction

theorem Nat.lt_of_le_of_lt (a b c: Nat) (hab: a ≤ b) (hbc: b < c): a < c := by 
  rw [Nat.le_iff] at hab 
  rw [Nat.lt_iff] at hbc
  rw [Nat.lt_iff]
  rcases hbc with ⟨hbcl,hbcr⟩
  rcases hab with ⟨ d,hd⟩
  rcases hbcl with ⟨e,he⟩
  constructor
  case left=>
    rw [he,hd]
    use d+e
    rw [Nat.add_assoc]
  case right =>
    by_contra h
    rw [h] at hd
    have hbc: b ≥ c := by 
      rw [Nat.ge_iff_le,Nat.le_iff]
      use d
    have hcb : c ≥ b := by 
      rw [Nat.ge_iff_le,Nat.le_iff]
      use e 
    have heq: b = c := by 
      apply Nat.ge_antisymm
      case hab => exact hbc
      case hba => exact hcb
    contradiction
       
theorem Nat.zero_le (a:Nat): 0 ≤ a := by 
  rw [Nat.le_iff]
  use a 
  rw [Nat.zero_add]

theorem Nat.trichotomous (a b:Nat): a<b ∨ a = b ∨ a > b := by 
  induction a 
  case zero =>
    have h: 0≤b := by 
      rw [Nat.le_iff_lt_or_eq]
      cases b
      case zero =>
        right 
        change 0 = 0
        rfl
      case succ c => 
        left 
        rw [← Nat.gt_iff_lt]
        apply Nat.succ_gt_zero        
    rw [Nat.le_iff_lt_or_eq] at h
    cases h
    case inl hl =>
      left 
      change 0 < b 
      exact hl 
    case inr hr =>
      right
      left 
      change 0 = b 
      exact hr 
  case succ c hc => 
    cases hc 
    case inl hc => 
      rw [Nat.lt_iff_succ_le] at hc
      rw [Nat.le_iff_lt_or_eq] at hc
      cases hc 
      case inl hc =>
        left
        exact hc 
      case inr hc =>
        right
        left
        exact hc
    case inr hc =>
      cases hc 
      case inl hc =>
        right
        right
        rw [hc]
        apply Nat.succ_gt_self
      case inr hc =>
        right
        right
        apply Nat.gt_trans (succ c) c b
        case hab => apply Nat.succ_gt_self
        case hbc => exact hc

def Nat.lt_of_succ (a b : Nat): succ a < succ b ↔ a < b := by 
  repeat rw [← Nat.succ_eq_add_one] 
  constructor 
  case mp => 
    intro h 
    rw [Nat.lt_iff] at h 
    rw [Nat.lt_iff]
    rcases h with ⟨hl,hr⟩
    rcases hl with ⟨c,hc⟩
    constructor 
    case left => 
      use c 
      apply Nat.add_right_cancel 1 b (a + c)
      rw [hc]
      repeat rw [Nat.succ_eq_add_one]
      rw [Nat.succ_add]
    case right => 
      by_contra
      rw [this] at hr 
      have h_con: b+1 = b+1 := by 
        apply Nat.add_cancel_left
        rfl
      contradiction
  case mpr => 
    intro h 
    rw [Nat.lt_iff]
    rw [Nat.lt_iff] at h
    rcases h with ⟨c_ex,neq⟩
    rcases c_ex with ⟨c,hc⟩
    constructor 
    case left =>
      use c 
      nth_rw 3 [Nat.add_comm]
      nth_rw 1 [Nat.add_comm]
      apply Nat.add_cancel_left 1 b (a+c)
      exact hc 
    case right =>
      by_contra
      apply Nat.add_right_cancel at this
      contradiction

def Nat.decLe: (a b: Nat) → Decidable (a≤b)
  | 0, b => by
    apply isTrue
    apply Nat.zero_le
  | succ a, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        by_contra h_con
        rw [Nat.le_iff] at h_con
        rcases h_con with ⟨c,hc⟩
        rw [h] at hc 
        nth_rw 1 [← Nat.add_zero b] at hc 
        rw [Nat.succ_add,← Nat.add_succ] at hc 
        apply Nat.add_left_cancel at hc 
        have hc_con: succ c≠0 := Nat.succ_ne c
        contradiction
      | isFalse hf =>
        apply isTrue
        rw [← Nat.lt_iff_succ_le]
        rw [Nat.le_iff] at h
        rcases h with ⟨c,hc⟩
        rw [Nat.lt_iff]
        constructor 
        case left => 
          use c 
        case right =>
          exact hf 
    | isFalse h =>
      apply isFalse
      rw [Nat.le_iff_lt_or_eq] 
      intro  ha
      contrapose h
      rw [Nat.le_iff_lt_or_eq]
      cases ha 
      case inl hl => 
        left
        apply Nat.lt_trans a (succ a) b
        case hab => 
          rw [← Nat.gt_iff_lt]
          apply Nat.succ_gt_self
        case hbc => exact hl 
      case inr hr =>
        left 
        rw [← hr,← Nat.gt_iff_lt]
        apply Nat.succ_gt_self

instance Nat.decidableRel : DecidableRel (·≤ ·: Nat → Nat → Prop) := Nat.decLe

instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := le_trans a b c hab hbc
  lt_iff_le_not_ge a b := by
    constructor
    case mp => 
      intro h 
      constructor 
      case left =>
        apply Nat.le_of_lt a b
        exact h 
      case right =>
        by_contra
        rw [Nat.le_iff_lt_or_eq b a] at this
        cases this 
        case inl hl =>
          have hab: a = b := by 
            rw [← Nat.gt_iff_lt] at h hl
            apply Nat.ge_of_gt at h 
            apply Nat.ge_of_gt at hl 
            apply Nat.ge_antisymm
            case hab => exact hl 
            case hba => exact h
          rw [Nat.lt_iff] at h
          rcases h with ⟨_,hr⟩
          contradiction
        case inr hr => 
          rw [Nat.lt_iff] at h
          rcases h with ⟨_,hl⟩
          symm at hl 
          contradiction
    case mpr =>
      intro h 
      rcases h with ⟨hl,hr⟩
      rw [Nat.le_iff_lt_or_eq] at hl
      contrapose hr 
      cases hl 
      case inl hl =>
        by_contra
        contradiction
      case inr hr =>
        rw [Nat.le_iff_lt_or_eq]
        right
        symm
        exact hr 

  le_antisymm a b hab hba := by 
    rw [← Nat.ge_iff_le] at hab hba
    apply Nat.ge_antisymm
    case hab => exact hba
    case hba => exact hab
  le_total a b := by
    have h: a<b ∨ a = b ∨ a>b := Nat.trichotomous a b
    cases h 
    case inl hl =>
      apply Nat.le_of_lt at hl 
      left
      exact hl 
    case inr hr =>
      cases hr 
      case inl hl =>
        rw [Nat.le_iff]
        left 
        use 0
        rw [Nat.add_zero]
        symm
        exact hl
      case inr hr =>
        rw [Nat.gt_iff_lt] at hr 
        right
        apply Nat.le_of_lt at hr 
        exact hr 
  toDecidableLE := decidableRel

example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by rw [Nat.add_zero]
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

theorem Nat.lt_squeeze (n m:Nat) (h1: n < m) (h2: m < succ n) : False:=by
    induction m
    case zero =>
      rw [Nat.lt_iff] at h1
      rcases h1 with ⟨hl,hr⟩
      rcases hl with ⟨a,ha⟩
      change 0 = n + a at ha 
      symm at ha 
      apply Nat.add_eq_zero at ha 
      change n ≠ 0 at hr 
      rcases ha with ⟨h_con,_⟩
      contradiction
    case succ m hm => 
      rw [← Nat.succ_eq_add_one,← Nat.succ_eq_add_one,← Nat.add_lt_add_left m n 1] at h2
      rw [Nat.lt_iff] at h1 h2 
      rcases h1 with ⟨h1l,h1r⟩
      rcases h1l with ⟨a,ha⟩
      rcases h2 with ⟨h2l,h2r⟩
      rcases h2l with ⟨b,hb⟩
      rw [hb,← Nat.succ_eq_add_one,Nat.add_assoc] at ha
      apply Nat.add_left_cancel at ha 
      have h:a=1 ∨ b=1 := by 
        induction a 
        case zero => 
          change 1 = b + 0 at ha 
          rw [Nat.add_zero] at ha 
          right 
          symm
          exact ha 
        case succ a ha2 =>
          rw [← Nat.zero_succ] at ha
          change succ 0 = b + succ a at ha 
          rw [Nat.add_succ] at ha
          apply Nat.succ_cancel at ha 
          symm at ha
          apply Nat.add_eq_zero at ha 
          left 
          rcases ha with ⟨_,ha⟩
          rw [ha]
          rfl
      cases h
      case inl h =>
        rw [h] at ha 
        nth_rw 1 [← Nat.zero_add 1] at ha 
        apply Nat.add_right_cancel at ha 
        rw [← ha,Nat.add_zero] at hb
        symm at hb 
        contradiction
      case inr h =>
        rw [h,Nat.succ_eq_add_one] at hb
        contradiction

def Nat.ns_mul: _root_.Nat → Nat → Nat 
  | 0,_ => zero
  | m+1,n => Nat.ns_mul m n + n

instance Nat.isCommMonoid: AddCommMonoid Nat where 
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  nsmul := Nat.ns_mul


instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (add_le_add_left a b c).mp hab

theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by sorry
#check Nat.strong_induction

theorem Nat.backwards_induction {n:Nat} {P:Nat → Prop}
  (hind: ∀ m, P (succ m) → P m) (hn: P n): 
    ∀ m, m  ≤ n → P m := by
      intro m hm 
      rw [Nat.le_iff] at hm 
      rcases hm with ⟨a,ha⟩
      induction a  generalizing m
      case zero => 
        change n = m + 0 at ha
        rw [Nat.add_zero] at ha 
        rw [← ha]
        exact hn 
      case succ a ha_ind =>
        apply hind
        rw [Nat.add_succ] at ha 
        apply ha_ind
        rw [← Nat.succ_add] at ha 
        exact ha 

theorem Nat.induction_from {n:Nat} {P:Nat → Prop}
  (hind:∀ m, P m → P (succ m)): 
    P n → ∀ m, m ≥ n → P m := by 
    intro hn m hm
    rw [Nat.ge_iff_le, Nat.le_iff] at hm 
    rcases hm with ⟨a,ha⟩
    induction a generalizing n 
    case zero =>
      change m = n + 0 at ha 
      rw [Nat.add_zero] at ha 
      rw [ha]
      exact hn
    case succ a ha_ind => 
      rw [Nat.add_succ,← Nat.succ_add] at ha 
      have hn2 : P (succ n) := by 
        apply hind
        exact hn
      apply ha_ind at hn2
      apply hn2 at ha
      exact ha 
end MyNat
