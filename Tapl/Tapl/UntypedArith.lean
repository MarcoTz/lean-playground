import Std.Data.HashSet
import Init.Data.LawfulHashable
import Mathlib.Tactic

namespace UntypedArith

  inductive Term: Type where 
  | Tru: Term
  | Fls: Term
  | IfT: Term → Term → Term → Term
  | Z: Term
  | Succ: Term → Term 
  | Pred: Term → Term
  | IsZero: Term → Term
  deriving BEq, ReflBEq, LawfulBEq, Hashable

  def consts: Term → Std.HashSet Term
  | Term.Tru => Std.HashSet.ofList [Term.Tru]
  | Term.Fls => Std.HashSet.ofList [Term.Fls]
  | Term.IfT cond thent elset => 
    ((consts cond).union (consts thent)).union (consts elset)
  | Term.Z => Std.HashSet.ofList [Term.Z]
  | Term.Succ t => consts t 
  | Term.Pred t => consts t 
  | Term.IsZero t => consts t 

  def size: Term → Nat 
    | Term.Tru => 1 
    | Term.Fls => 1 
    | Term.IfT cond thent elset => 1 + size cond + size thent + size elset
    | Term.Z => 1 
    | Term.Succ t => 1 + size t 
    | Term.Pred t => 1 + size t 
    | Term.IsZero t => 1 + size t 

  def depth: Term → Nat 
    | Term.Tru => 1
    | Term.Fls => 1 
    | Term.IfT cond thent elset => ((depth cond).max (depth thent)).max (depth elset)
    | Term.Z => 1 
    | Term.Succ t => 1 + depth t 
    | Term.Pred t => 1 + depth t 
    | Term.IsZero t => 1 + depth t 

  lemma depth_ne_zero: ∀ (t:Term), depth t ≠ 0 := by 
    intro t 
    induction t 
    case IfT cond thent elset h_cond h_then h_else => 
      simp [depth]
      intros
      contradiction
    repeat (simp [depth])

  lemma consts_lt_size: ∀ (t:Term), (consts t).size ≤ size t := by 
    intro t 
    induction t 
    case IfT cond thent elset h_cond h_then h_else =>
      simp [consts,size]
      apply Nat.le_trans (m:=(consts cond ∪ consts thent).size + (consts elset).size)
      case _ =>
        apply Std.HashSet.size_union_le_size_add_size
      case _ =>
        apply Nat.le_trans (m:= (consts cond).size + (consts thent).size + (consts elset).size)
        case _ =>
          simp
          apply Std.HashSet.size_union_le_size_add_size
        case _ =>
          apply Nat.le_trans (m:= size cond + (consts thent).size + (consts elset).size)
          case _ =>
            simp; exact h_cond
          case _ =>
            apply Nat.le_trans (m:= size cond + size thent + (consts elset).size)
            case _ =>
              simp
              exact h_then
            case _ =>
              apply Nat.le_trans (m:=size cond + size thent + size elset)
              case _ =>
                simp; exact h_else
              case _ =>
                simp
    case Succ t ht =>
      simp [consts,size]
      apply Nat.le_trans (m:= size t)
      case _ => exact ht 
      case _ => omega
    case Pred t ht =>
      simp [consts,size]
      apply Nat.le_trans (m:= size t)
      case _ => exact ht 
      case _ => omega
    case IsZero t ht =>
      simp [consts,size]
      apply Nat.le_trans (m:= size t)
      case _ => exact ht 
      case _ => omega
    repeat (simp [consts,size]; apply Std.HashSet.size_insert_le)


  theorem depth_induction: ∀ (P: Term → Prop) 
    (_:∀ (t:Term), (∀ (s:Term), depth s < depth t → P s) → P t),
    ∀ t:Term, P t := by 
    intro P h_ind t
    induction h: depth t using Nat.strong_induction_on generalizing t 
    case h n hn =>
      apply h_ind 
      intro s hs 
      rw [← h] at hn
      apply hn  (depth s)
      case _ => exact hs 
      case _ => rfl

  theorem size_induction: ∀ (P:Term → Prop)
    (_:∀ (t:Term), (∀ (s:Term), size s < size t → P s) → P t),
    ∀ t:Term, P t := by
      intro P h_ind t 
      induction h:size t using Nat.strong_induction_on generalizing t 
      case h n hn =>
        apply h_ind 
        intro s hs 
        rw [← h] at hn 
        apply hn (size s)
        case _ => exact hs 
        case _ => rfl

  inductive SubTerm: Term → Term → Prop where 
  | subIfCond (cond thent elset: Term):
    SubTerm cond (Term.IfT cond thent elset)
  | subIfThen (cond thent elset: Term):
    SubTerm thent (Term.IfT cond thent elset)
  | subIfElse (cond thent elset: Term):
    SubTerm elset (Term.IfT cond thent elset)
  | subSucc (t:Term):
    SubTerm t (Term.Succ t)
  | subPred (t:Term):
    SubTerm t (Term.Pred t)
  | subIsZero (t:Term):
    SubTerm t (Term.IsZero t)
  
  theorem strucutral_induction: ∀ (P:Term → Prop)
  (_: ∀ (t:Term), (∀ (s:Term), SubTerm s t → P s) → P t),
  ∀ (t:Term), P t := by 
  intro P h_ind t 
  induction t <;> (apply h_ind; intro s hs; cases hs)
  case IfT.a.subIfCond cond thent elset h_cond h_then h_else => exact h_cond
  case IfT.a.subIfThen cond thent elset h_cond h_then h_else => exact h_then
  case IfT.a.subIfElse cond thent elset h_cond h_then h_else => exact h_else
  case Succ.a.subSucc t ht => exact ht
  case Pred.a.subPred t ht => exact ht 
  case IsZero.a.subIsZero t ht => exact ht

  inductive NumericValue:Term → Prop where 
  | valueZ: NumericValue Term.Z
  | valueSucc (t:Term): NumericValue t → NumericValue (Term.Succ t)

  lemma num_val_inversion: ∀ (t:Term), NumericValue t → 
    t = Term.Z ∨ ∃ (s:Term), NumericValue s ∧ t = Term.Succ s := by 
    intro t ht 
    cases ht 
    case valueZ => left; rfl 
    case valueSucc s hs => right; use s;

  inductive Value: Term → Prop where 
  | valueTrue: Value Term.Tru
  | valueFalse: Value Term.Fls
  | valueNum (t:Term): NumericValue t → Value t

  lemma val_inversion: ∀ (t:Term), Value t → 
  t = Term.Tru ∨ t = Term.Fls ∨ NumericValue t := by 
    intro t ht 
    cases ht 
    case valueTrue => left; rfl
    case valueFalse => right; left; rfl 
    case valueNum h => right;right;exact h
 
  inductive Eval: Term → Term → Prop where 
  | evalIfTrue (thent elset:Term):
    Eval (Term.IfT Term.Tru thent elset) thent
  | evalIfFalse (thent elset:Term):
    Eval (Term.IfT Term.Fls thent elset) elset
  | evalIfCong (cond₁ cond₂ thent elset:Term):
    Eval cond₁ cond₂ → 
    Eval (Term.IfT cond₁ thent elset) (Term.IfT cond₂ thent elset)
  | evalSuccCong (t₁ t₂:Term):
    Eval t₁ t₂ → Eval (Term.Succ t₁) (Term.Succ t₂)
  | evalPredZero: 
    Eval (Term.Pred Term.Z) Term.Z
  | evalPredSucc (t:Term):
    NumericValue t → Eval (Term.Pred (Term.Succ t)) t 
  | evalPredCong (t₁ t₂:Term):
    Eval t₁ t₂ → Eval (Term.Pred t₁) (Term.Pred t₂)
  | evalIsZeroZero:
    Eval (Term.IsZero (Term.Z)) Term.Tru
  | evalIsZeroSucc (t:Term):
    NumericValue t → 
    Eval (Term.IsZero (Term.Succ t)) Term.Fls
  | evalIsZeroCong (t₁ t₂:Term):
    Eval t₁ t₂ → 
    Eval (Term.IsZero t₁) (Term.IsZero t₂)

  lemma eval_if_inversion: ∀ (cond thent elset s:Term), 
    Eval (Term.IfT cond thent elset) s → 
      (cond=Term.Tru ∧ s = thent) ∨ 
      (cond = Term.Fls ∧ s = elset) ∨ 
      ∃ (cond₂:Term), Eval cond cond₂ ∧ s = Term.IfT cond₂ thent elset := by 
      intro cond thent elset s h_eval
      cases h_eval
      case evalIfTrue => 
        left 
        constructor 
        case h.left => rfl
        case h.right => rfl
      case evalIfFalse =>
        right
        left 
        constructor
        case _ => rfl
        case _ => rfl
      case evalIfCong cond₂ h_cond₂ =>
        right 
        right 
        use cond₂

  lemma eval_pred_inversion:∀(t s:Term), Eval (Term.Pred t) s → 
    (s = Term.Z ∧ t = Term.Z) ∨ 
    (∃ (t₂:Term), s = t₂ ∧ t = Term.Succ t₂) ∨ 
    (∃ t₂:Term, Eval t t₂ ∧ s = Term.Pred t₂) := by 
    intro t s h_eval 
    cases h_eval
    case evalPredZero => 
      left 
      constructor
      rfl;rfl
    case evalPredSucc nv => 
      right 
      left 
      use s 
    case evalPredCong t₂ ht₂ => 
      right;right
      use t₂

  
  def NormalForm: Term → Prop := λ t => ∀ (s:Term), ¬ (Eval t s)

  theorem value_normal: ∀ (t:Term), Value t → NormalForm t := by 
    intro t h_val s 
    by_contra
    induction t generalizing s 
    case Tru => cases this 
    case Fls => cases this 
    case IfT cond thent elset h_cond h_then h_else =>
      cases h_val 
      case valueNum hn => cases hn 
    case Z => cases this 
    case Pred t ht => 
      cases h_val
      case valueNum hn => cases hn 
    case IsZero => 
      cases h_val 
      case valueNum hn => cases hn 
    case Succ t ht => 
      cases this 
      case evalSuccCong t₃ h₃ =>
        cases h_val 
        case valueNum hn =>
          cases hn
          case valueSucc hn =>
            have h: Value t := by 
              constructor 
              exact hn
            apply ht at h
            apply h t₃ 
            exact h₃ 
    

  theorem eval_det: ∀ (t₁ t₂ t₃ :Term), Eval t₁ t₂ → Eval t₁ t₃ → t₂ = t₃ := by 
  intro t₁ t₂ t₃ h₂ h₃ 
  induction h₂ generalizing t₃
  case evalIfTrue elset =>
    cases h₃ 
    case evalIfTrue => rfl
    case evalIfCong cond₂ h_cond₂ => cases h_cond₂ 
  case evalIfFalse thent =>
    cases h₃ 
    case evalIfFalse => rfl
    case evalIfCong cond₂ h_cond₂ => cases h_cond₂ 
  case evalIfCong cond₁ cond₂ thent elset h_cond h_ind =>
    cases h₃ 
    case evalIfTrue => cases h_cond
    case evalIfFalse => cases h_cond
    case evalIfCong cond₃ h_cond₃ =>
      simp
      apply h_ind 
      exact h_cond₃ 
  case evalSuccCong t₄ t₅ h₄ h_ind =>
    cases h₃ 
    case evalSuccCong t₆ h₆ =>
      simp 
      apply h_ind 
      exact h₆ 
  case evalPredZero =>
    cases h₃ 
    case evalPredZero => rfl
    case evalPredCong t₃ h₃ => cases h₃ 
  case evalPredSucc t₄ h₄ =>
    cases h₃ 
    case evalPredSucc => rfl 
    case evalPredCong t₅ h₅ =>
      cases h₅ 
      case evalSuccCong t₆ h₆ =>
        have h: ¬ Eval t₄ t₆ := by 
          apply value_normal
          constructor
          exact h₄ 
        contradiction
  case evalPredCong t₄ t₅ h₄ h_ind =>
    cases h₃ 
    case evalPredZero => cases h₄ 
    case evalPredSucc h_val => 
      cases h₄ 
      case evalSuccCong t₅ h₅ =>
        have h: ¬ Eval t₃ t₅ := by 
          apply value_normal
          constructor
          exact h_val
        contradiction
    case evalPredCong t₆ h₆ =>
      simp 
      apply h_ind 
      exact h₆ 
  case evalIsZeroZero =>
    cases h₃ 
    case evalIsZeroZero => rfl
    case evalIsZeroCong t₃ h₃ => cases h₃ 
  case evalIsZeroSucc t₄ h₄ =>
    cases h₃ 
    case evalIsZeroSucc => rfl
    case evalIsZeroCong t₅ h₅ =>
      cases h₅ 
      case evalSuccCong t₆ h₆ =>
        have h: ¬ Eval t₄ t₆ := by 
          apply value_normal
          constructor
          exact h₄ 
        contradiction
  case evalIsZeroCong t₄ t₅ h₄ h₅ =>
    cases h₃ 
    case evalIsZeroZero => cases h₄ 
    case evalIsZeroSucc t₆ h₆ =>
      cases h₄ 
      case evalSuccCong t₇ h₇ =>
        have h: ¬ Eval t₆ t₇ := by 
          apply value_normal
          constructor
          exact h₆ 
        contradiction
    case evalIsZeroCong t₆ h₆ =>
      simp 
      apply h₅ 
      exact h₆ 
     

  inductive EvalStar: Term → Term → Prop where 
  | evalSingle (t₁ t₂: Term):
    Eval t₁ t₂ → EvalStar t₁ t₂
  | evalRefl (t:Term):
    EvalStar t t
  | evalTrans (t₁ t₂ t₃:Term):
    Eval t₁ t₂ → EvalStar t₂ t₃ → EvalStar t₁ t₃ 

  lemma evalstar_trans: ∀ (t₁ t₂ t₃ : Term), EvalStar t₁ t₂ → EvalStar t₂ t₃ → EvalStar t₁ t₃ := by 
    intro t₁ t₂ t₃ h₁₂ h₂₃ 
    induction h₁₂
    case evalSingle t₄ t₅ h₄₅ =>
      apply EvalStar.evalTrans t₄ t₅ t₃ h₄₅ h₂₃
    case evalRefl => exact h₂₃ 
    case evalTrans t₄ t₅ t₆ h₄₅ h₅₆ h_ind =>
      apply h_ind at h₂₃ 
      apply EvalStar.evalTrans t₄ t₅ t₃ h₄₅ h₂₃ 


  lemma evalstar_normal: ∀ (t₁ t₂:Term), NormalForm t₁ → EvalStar t₁ t₂ → t₁ = t₂ := by 
    intro t₁ t₂ h_norm h_eval
    induction h_eval
    case evalSingle t₃ t₄ h_eval => 
      unfold NormalForm at h_norm 
      specialize h_norm t₄
      contradiction
    case evalRefl => rfl 
    case evalTrans t₃ t₄ t₅ h_eval₃₄ h_eval₄₅ h_ind₃ =>
      unfold NormalForm at h_norm
      specialize h_norm t₄ 
      contradiction

  theorem normal_unique: ∀ (t₁ t₂ t₃:Term),
    NormalForm t₂ → NormalForm t₃ → 
    EvalStar t₁ t₂ → EvalStar t₁ t₃ → 
    t₂ = t₃ := by 
      intro t₁ t₂ t₃ h₂ h₃ h₁₂ h₁₃ 
      induction h₁₂ 
      case evalSingle t₄ t₅ h₄₅ =>
        cases h₁₃ 
        case evalSingle h₄₃ =>
          apply eval_det t₄ t₅ t₃ h₄₅ h₄₃ 
        case evalRefl => 
          unfold NormalForm at h₃ 
          specialize h₃ t₅ 
          contradiction
        case evalTrans t₆ h₄₆ h₆₃=>
          have h:= eval_det t₄ t₅ t₆ h₄₅ h₄₆ 
          rw [← h] at h₆₃ 
          exact evalstar_normal t₅ t₃ h₂ h₆₃ 
      case evalRefl t₄ =>
        apply evalstar_normal t₄ t₃ h₂ h₁₃ 
      case evalTrans t₄ t₅ t₆ h₄₅ h₅₆ h_ind₆ =>
        apply h_ind₆ h₂ 
        cases h₁₃ 
        case evalSingle h₄₃ =>
          have h:=eval_det t₄ t₅ t₃ h₄₅ h₄₃ 
          rw [h] 
          apply EvalStar.evalRefl 
        case evalRefl => 
          unfold NormalForm at h₃ 
          specialize h₃ t₅ 
          contradiction
        case evalTrans t₇ h₄₇ h₇₃ =>
          have h := eval_det t₄ t₅ t₇ h₄₅ h₄₇ 
          rw [← h] at h₇₃ 
          exact h₇₃ 

    lemma eval_step: ∀ (t:Term), NormalForm t ∨ ∃ (s:Term), Eval t s := by 
    intro t 
    induction t 
    case Tru => 
      left 
      apply value_normal
      constructor
    case Fls => 
      left 
      apply value_normal
      constructor
    case IfT cond thent elset h_cond h_then h_else => 
      cases h_cond 
      case inl h =>
        by_cases Value cond 
        case pos h_cond =>
          cases h_cond 
          case valueTrue =>
            right 
            use thent
            constructor
          case valueFalse =>
            right 
            use elset 
            constructor
          case valueNum h_num =>
            left 
            by_contra! 
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            apply eval_if_inversion at hx 
            cases hx 
            case h.inl h =>
              rcases h with ⟨hl,hr⟩
              cases h:h_num
              case valueZ => contradiction
              case valueSucc => contradiction
            case h.inr h  =>
              cases h 
              case inl h₂ =>
                rcases h₂ with ⟨hl,hr⟩
                cases h_num:h_num
                case valueZ => contradiction
                case valueSucc => contradiction
              case inr h₂ =>
                rcases h₂ with ⟨cond₂, h_cond₂⟩
                rcases h_cond₂ with ⟨h_eval,h_x⟩
                simp [NormalForm] at h 
                specialize h cond₂ 
                contradiction
        case neg h_noval =>
          left 
          by_contra!
          simp [NormalForm] at this 
          rcases this with ⟨x,hx⟩
          cases hx 
          case h.evalIfTrue =>
            have h: Value Term.Tru := by constructor
            contradiction
          case h.evalIfFalse =>
            have h: Value Term.Fls := by constructor
            contradiction
          case h.evalIfCong cond₂ h_cond₂ =>
            unfold NormalForm at h 
            specialize h cond₂ 
            contradiction
      case inr h =>
        rcases h with ⟨cond₂,h_cond₂⟩
        right 
        use (Term.IfT cond₂ thent elset)
        constructor
        exact h_cond₂ 
    case Z => 
      left 
      apply value_normal
      constructor
      constructor
    case Succ t h_t =>
      cases h_t 
      case inl h_t =>
        left 
        unfold NormalForm
        by_contra!
        rcases this with ⟨x,hx⟩
        cases hx 
        case h.evalSuccCong t₂ ht₂ => 
        unfold NormalForm at h_t 
        specialize h_t t₂ 
        contradiction
      case inr h_t =>
        rcases h_t with ⟨x,hx⟩
        right 
        use (Term.Succ x)
        constructor
        exact hx 
    case Pred t h_t =>
      cases h_t
      case inl h_t =>
        by_cases Value t 
        case pos h_val =>
          cases h_val
          case valueTrue =>
            left 
            by_contra
            unfold NormalForm at this 
            simp at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case h.evalPredCong t₂ ht₂ =>
            cases ht₂ 
          case valueFalse =>
            left 
            by_contra
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            rcases hx 
            case h.evalPredCong t₂ ht₂ =>
              cases ht₂
          case valueNum h_num =>
            cases h_num
            case valueZ =>
              right 
              use Term.Z 
              constructor
            case valueSucc t h_num =>
              right
              use t
              constructor
              exact h_num
        case neg h_no =>
          left 
          by_contra
          unfold NormalForm at this 
          simp at this 
          rcases this with ⟨x,hx⟩
          cases hx 
          case h.evalPredZero =>
            have h: Value Term.Z := by constructor;constructor
            contradiction
          case h.evalPredSucc num =>
            have h: Value (Term.Succ x) := by 
              constructor
              constructor
              exact num
            contradiction
          case h.evalPredCong t₂ ht₂ =>
            unfold NormalForm at h_t 
            specialize h_t t₂ 
            contradiction
      case inr h =>
        rcases h with ⟨x,hx⟩
        right
        use (Term.Pred x)
        constructor
        exact hx 
    case IsZero t h_t =>
      cases h_t 
      case inl h_t =>
        by_cases Value t 
        case pos h_val =>
          cases h_val
          case valueTrue =>
            left 
            by_contra
            unfold NormalForm at this 
            simp at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case h.evalIsZeroCong t₂ ht₂ =>
            cases ht₂ 
          case valueFalse =>
            left 
            by_contra
            simp [NormalForm] at this
            rcases this with ⟨x,hx⟩
            cases hx 
            case h.evalIsZeroCong t₂ ht₂ =>
              cases ht₂ 
          case valueNum h_num =>
            cases h_num
            case valueZ =>
              right 
              use Term.Tru
              constructor
            case valueSucc t₂ h_num =>
              right 
              use Term.Fls
              constructor
              exact h_num
        case neg h_no =>
          left 
          by_contra
          simp [NormalForm] at this 
          rcases this with ⟨x,hx⟩
          cases hx 
          case h.evalIsZeroZero =>
            have h: Value Term.Z := by constructor;constructor
            contradiction
          case h.evalIsZeroSucc t₂ h_num =>
            have h: Value (Term.Succ t₂) := by constructor;constructor;exact h_num
            contradiction
          case h.evalIsZeroCong t₂ ht₂ =>
            unfold NormalForm at h_t 
            specialize h_t t₂ 
            contradiction
      case inr h_t =>
        rcases h_t with ⟨x,hx⟩
        right 
        use (Term.IsZero x)
        constructor
        exact hx 

    lemma evalstar_if_cong: ∀ (cond cond₂ thent elset:Term), EvalStar cond cond₂ → EvalStar (Term.IfT cond thent elset) (Term.IfT cond₂ thent elset) := by 
      intro cond cond₂ thent elset h_cond 
      induction h_cond 
      case evalSingle t₁ t₂ h_cond => constructor; constructor; exact h_cond
      case evalRefl t => apply EvalStar.evalRefl
      case evalTrans t₁ t₂ t₃ h₁₂ h₂₃ h_ind =>
        apply EvalStar.evalTrans (t₂:= Term.IfT t₂ thent elset)
        case _ => constructor; exact h₁₂ 
        case _ => exact h_ind 

    lemma evalstar_succ_cong: ∀ (t₁ t₂:Term), EvalStar t₁ t₂ → EvalStar (Term.Succ t₁) (Term.Succ t₂) := by 
      intro t₁ t₂ h₁₂ 
      induction h₁₂ 
      case evalSingle t₃ t₄ h₃₄ => constructor; constructor; exact h₃₄ 
      case evalRefl t₃ => apply EvalStar.evalRefl
      case evalTrans t₃ t₄ t₅ h₃₄ h₄₅ h_ind =>
        apply EvalStar.evalTrans (t₂ := Term.Succ t₄) 
        case _ => constructor; exact h₃₄ 
        case _ => exact h_ind

    lemma evalstar_pred_cong: ∀ (t₁ t₂:Term), EvalStar t₁ t₂ → EvalStar (Term.Pred t₁) (Term.Pred t₂) := by 
      intro t₁ t₂ h₁₂ 
      induction h₁₂ 
      case evalSingle t₃ t₄ h₃₄ => constructor; constructor; exact h₃₄ 
      case evalRefl t₃ => apply EvalStar.evalRefl 
      case evalTrans t₃ t₄ t₅ h₃₄ h₄₅ h_ind =>
        apply EvalStar.evalTrans (t₂:= Term.Pred t₄)
        case _ => constructor; exact h₃₄ 
        case _ => exact h_ind 

    lemma evalstar_iszero_cong: ∀ (t₁ t₂:Term), EvalStar t₁ t₂ → EvalStar (Term.IsZero t₁) (Term.IsZero t₂) := by 
      intro t₁ t₂ h₁₂ 
      induction h₁₂ 
      case evalSingle t₃ t₄ h₃₄ => constructor; constructor; exact h₃₄ 
      case evalRefl t₃ => apply EvalStar.evalRefl
      case evalTrans t₃ t₄ t₅ h₃₄ h₄₅ h_ind =>
        apply EvalStar.evalTrans (t₂:=Term.IsZero t₄)
        case _ => constructor; exact h₃₄ 
        case _ => exact h_ind 

    theorem evalstar_term: ∀ (t:Term), ∃ (s:Term), NormalForm s ∧ EvalStar t s := by 
    intro t 
    induction t 
    case Tru => 
      use Term.Tru
      constructor 
      case h.left =>
        apply value_normal
        constructor
      case h.right =>
        apply EvalStar.evalRefl 
    case Fls => 
      use Term.Fls
      constructor
      case h.left =>
        apply value_normal
        constructor
      case h.right =>
        apply EvalStar.evalRefl
    case IfT cond thent elset h_cond h_then h_else =>
      rcases h_cond with ⟨cond₂, ⟨h_condl,hcondr⟩⟩
      rcases h_then with ⟨then₂, ⟨h_thenl,h_thenr⟩⟩
      rcases h_else with ⟨else₂, ⟨h_elsel,h_elser⟩⟩
      by_cases Value cond₂  
      case pos h_val =>
        cases h_val
        case valueTrue =>
          use then₂
          constructor
          case h.left => exact h_thenl
          case h.right => 
            apply evalstar_trans (Term.IfT cond thent elset) thent then₂
            case _ => 
              apply evalstar_trans (Term.IfT cond thent elset) (Term.IfT Term.Tru thent elset) thent
              case _ => 
                apply evalstar_if_cong 
                apply hcondr
              case _ => constructor; constructor
            case _ => exact h_thenr
        case valueFalse =>
          use else₂ 
          constructor
          case h.left =>
            exact h_elsel
          case h.right =>
            apply evalstar_trans (Term.IfT cond thent elset) elset else₂ 
            case _ =>
              apply evalstar_trans (Term.IfT cond thent elset) (Term.IfT Term.Fls thent elset)
              case _ =>
                apply evalstar_if_cong
                apply hcondr
              case _ =>
                constructor
                constructor
            case _ => 
              apply h_elser
        case valueNum h_num =>
          use (Term.IfT cond₂ thent elset)
          constructor
          case h.left =>
            by_contra
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case evalIfTrue => 
              apply evalstar_normal at hcondr
              case _ => 
                rw [← hcondr] at h_num
                cases h_num
                case valueZ => contradiction
                case valueSucc => contradiction
              case _ => 
                apply value_normal
                constructor
                cases h_num
            case evalIfFalse => 
              cases h_num
            case evalIfCong cond₃ h_cond₃ =>
              unfold NormalForm at h_condl
              specialize h_condl cond₃ 
              contradiction
          case h.right =>
            apply evalstar_if_cong 
            case _ => exact hcondr
      case neg h_no =>
        use Term.IfT cond₂ thent elset
        constructor
        case h.left =>
          by_contra!
          simp [NormalForm] at this 
          rcases this with ⟨x,hx⟩
          cases hx 
          case evalIfTrue =>
            have h: Value Term.Tru := by constructor
            contradiction
          case evalIfFalse =>
            have h: Value Term.Fls := by constructor
            contradiction
          case evalIfCong cond₃ h_cond₃ =>
            unfold NormalForm at h_condl
            specialize h_condl cond₃ 
            contradiction
        case h.right => 
          apply evalstar_if_cong
          apply hcondr
    case Z => 
      use Term.Z 
      constructor
      case h.left => apply value_normal; constructor; constructor;
      case h.right => apply EvalStar.evalRefl
    case Succ t h_t =>
      rcases h_t with ⟨x,hx⟩
      rcases hx with ⟨hxl,hxr⟩
      by_cases Value x 
      case pos h_val => 
        cases h_val 
        case valueTrue => 
          use (Term.Succ Term.Tru)
          constructor
          case h.left => 
            by_contra
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case evalSuccCong t₂ ht₂ =>
              cases ht₂ 
          case h.right =>
            apply evalstar_succ_cong 
            exact hxr 
        case valueFalse => 
          use (Term.Succ Term.Fls) 
          constructor
          case h.left =>
            by_contra 
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case evalSuccCong t₂ ht₂ =>
              cases ht₂ 
          case h.right =>
            apply evalstar_succ_cong
            exact hxr 
        case valueNum h =>
          cases h
          case valueZ => 
            use (Term.Succ Term.Z)
            constructor
            case h.left =>
              apply value_normal
              constructor
              constructor
              constructor
            case h.right =>
              apply evalstar_succ_cong
              exact hxr 
          case valueSucc t₂ ht₂ =>
            use (Term.Succ (Term.Succ t₂))
            constructor
            case h.left =>
              apply value_normal
              constructor
              constructor
              constructor
              exact ht₂ 
            case h.right =>
              apply evalstar_succ_cong
              exact hxr 
      case neg h_no =>
        use (Term.Succ x)
        constructor
        case h.left =>
          by_contra
          simp [NormalForm] at this 
          rcases this with ⟨x₂,hx₂⟩
          cases hx₂ 
          case evalSuccCong x₃ hx₃  =>
            unfold NormalForm at hxl
            specialize hxl x₃ 
            contradiction
        case h.right =>
          apply evalstar_succ_cong
          exact hxr 
    case Pred t ht =>
      rcases ht with ⟨x,hx⟩
      rcases hx with ⟨hxl,hxr⟩
      by_cases Value x 
      case pos h_val =>
        cases h_val 
        case valueTrue =>
          use (Term.Pred Term.Tru)
          constructor
          case _ => 
            by_contra
            simp [NormalForm] at this 
            rcases this with ⟨x₂,hx₂⟩
            cases hx₂ 
            case evalPredCong t₂ ht₂ =>
              unfold NormalForm at hxl 
              specialize hxl t₂ 
              contradiction
          case h.right =>
            apply evalstar_pred_cong 
            exact hxr 
        case valueFalse =>
          use (Term.Pred Term.Fls)
          constructor
          case h.left =>
            by_contra
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case evalPredCong t₂ ht₂=>
            unfold NormalForm at hxl
            specialize hxl t₂ 
            contradiction
          case h.right =>
            apply evalstar_pred_cong 
            exact hxr 
        case valueNum h_val =>
          cases h_val 
          case valueZ =>
            use Term.Z 
            constructor 
            case h.left =>
              apply value_normal
              constructor
              constructor
            case h.right =>
              apply evalstar_trans (Term.Pred t) (Term.Pred Term.Z) Term.Z 
              case _ =>
                apply evalstar_pred_cong 
                exact hxr 
              case _ =>
                constructor
                constructor
          case valueSucc n hn =>
            use n
            constructor
            case h.left =>
              apply value_normal
              constructor
              exact hn
            case h.right =>
              apply evalstar_trans (Term.Pred t) (Term.Pred (Term.Succ n)) n
              case _ =>
                apply evalstar_pred_cong 
                exact hxr 
              case _ =>
                constructor
                constructor
                exact hn
      case neg h_no =>
        use Term.Pred x
        constructor 
        case h.left =>
          by_contra
          simp [NormalForm] at this 
          rcases this with ⟨x₂,hx₂⟩
          cases hx₂ 
          case evalPredZero =>
            have h:Value Term.Z := by constructor; constructor
            contradiction
          case evalPredSucc nv =>
            have h: Value (Term.Succ x₂) := by constructor;constructor; exact nv 
            contradiction
          case evalPredCong t₂ ht₂ =>
            unfold NormalForm at hxl 
            specialize hxl t₂ 
            contradiction
        case h.right =>
          apply evalstar_pred_cong 
          exact hxr 
    case IsZero t ht =>
      rcases ht with ⟨x,hx⟩
      rcases hx with ⟨hxl,hxr⟩
      by_cases Value x 
      case pos h_val =>
        cases h_val 
        case valueTrue => 
          use (Term.IsZero Term.Tru)
          constructor 
          case h.left =>
            by_contra
            simp [NormalForm] at this 
            rcases this with ⟨x,hx⟩
            cases hx 
            case evalIsZeroCong t₂ ht₂ => 
              cases ht₂ 
          case h.right =>
            apply evalstar_iszero_cong
            exact hxr 
        case valueFalse =>
          use (Term.IsZero Term.Fls)
          constructor
          case h.left =>
              by_contra
              simp [NormalForm] at this 
              rcases this with ⟨x,hx⟩
              cases hx 
              case evalIsZeroCong t₂ ht₂ =>
                cases ht₂ 
          case h.right =>
            apply evalstar_iszero_cong 
            exact hxr 
        case valueNum h_val =>
          cases h_val 
          case valueZ =>
            use Term.Tru
            constructor
            case h.left => 
              apply value_normal
              constructor
            case h.right =>
              apply evalstar_trans (Term.IsZero t) (Term.IsZero Term.Z) Term.Tru
              case _ =>
                apply evalstar_iszero_cong 
                exact hxr 
              case _ =>
                constructor
                constructor
          case valueSucc n hn =>
            use Term.Fls
            constructor
            case h.left =>
              apply value_normal
              constructor
            case h.right =>
              apply evalstar_trans (Term.IsZero t) (Term.IsZero (Term.Succ n)) Term.Fls
              case _ => 
                apply evalstar_iszero_cong 
                exact hxr 
              case _ =>
                constructor
                constructor
                exact hn
      case neg h_no =>
        use (Term.IsZero x)
        constructor
        case h.left =>
          by_contra
          simp [NormalForm] at this 
          rcases this with ⟨x₂,hx₂⟩
          cases hx₂ 
          case evalIsZeroZero =>
            have h: Value Term.Z := by constructor; constructor
            contradiction
          case evalIsZeroSucc t₂ ht₂ =>
            have h: Value (Term.Succ t₂) := by constructor; constructor; exact ht₂
            contradiction
          case evalIsZeroCong t₂ ht₂ =>
            unfold NormalForm at hxl 
            specialize hxl t₂ 
            contradiction
        case h.right =>
          apply evalstar_iszero_cong 
          exact hxr 
            
  inductive EvalBig: Term → (t:Term) → Value t → Prop  
  | bigVal (t:Term) (h:Value t): EvalBig t t h
  | bigIfTrue (t₁ t₂ t₃ v₂: Term) (h:Value v₂): 
    EvalBig t₁ Term.Tru (by constructor) → 
    EvalBig t₂ v₂ h → EvalBig (Term.IfT t₁ t₂ t₃) v₂ h
  | bigIfFalse (t₁ t₂ t₃ v₂: Term) (h:Value v₂):
    EvalBig t₁ Term.Fls (by constructor) → 
    EvalBig t₃ v₂ h → EvalBig (Term.IfT t₁ t₂ t₃) v₂ h 
  | bigSucc (t₁ nv₁: Term) (h:NumericValue nv₁):
    EvalBig t₁ nv₁ (by constructor; exact h) → 
    EvalBig (Term.Succ t₁) (Term.Succ nv₁) (by constructor; constructor; exact h)
  | bigPredZero (t₁:Term): 
    EvalBig t₁ Term.Z (by constructor;constructor) → 
    EvalBig (Term.Pred t₁) Term.Z (by constructor;constructor)
  | bigPredSucc (t₁ nv₁:Term) (h: NumericValue nv₁):
    EvalBig t₁ (Term.Succ nv₁) (by constructor;constructor;exact h) → 
    EvalBig (Term.Pred t₁) nv₁ (by constructor; exact h)
  | bigIsZeroZero (t₁:Term):
    EvalBig t₁ Term.Z (by constructor;constructor) → 
    EvalBig (Term.IsZero t₁) Term.Tru (by constructor)
  | bigIsZeroSucc (t₁ nv₁:Term) (h:NumericValue nv₁):
    EvalBig t₁ (Term.Succ nv₁) (by constructor;constructor;exact h) → 
    EvalBig (Term.IsZero t₁) Term.Fls (by constructor)

  lemma eval_big_val: ∀ (t v: Term) (h: Value v), Value t → EvalBig t v h → t = v := by 
    intro t v hv ht h_eval
    induction h_eval 
    case bigVal => rfl
    case bigIfTrue => cases ht; case valueNum h => cases h
    case bigIfFalse => cases ht; case valueNum h => cases h
    case bigSucc t₁ nv₁ hnv htnv h_ind=>
      simp 
      apply h_ind 
      cases ht 
      case valueNum h => 
        cases h 
        case valueSucc h => 
        constructor
        exact h
    case bigPredZero =>  cases ht; case valueNum h => cases h 
    case bigPredSucc => cases ht; case valueNum h => cases h
    case bigIsZeroZero => cases ht; case valueNum h => cases h
    case bigIsZeroSucc => cases ht; case valueNum h => cases h

  lemma eval_val_eval_big: ∀ (t v:Term) (h:Value v), Eval t v → EvalBig t v h:= by
    intro t v h h_eval
    induction h_eval
    case evalIfTrue elset =>
      apply EvalBig.bigIfTrue 
      case _ => constructor
      case _ => constructor
    case evalIfFalse thent elset =>
      apply EvalBig.bigIfFalse 
      case _ => constructor
      case _ => constructor
    case evalIfCong cond₁ cond₂ thent elset h_cond h_ind =>
      cases h
      case valueNum h =>
        cases h
    case evalSuccCong t₁ t₂ h₁₂ h_ind =>
      apply EvalBig.bigSucc 
      case _ => apply h_ind 
      case _ => 
        cases h; case valueNum h => cases h; case valueSucc h => exact h 
    case evalPredZero =>
      apply EvalBig.bigPredZero
      constructor
    case evalPredSucc t₁ ht₂ =>
      apply EvalBig.bigPredSucc
      case _ =>
        constructor
      case _ =>
        exact ht₂ 
    case evalPredCong t₁ t₂ h₁₂ h_ind =>
      cases h
      case valueNum h => cases h
    case evalIsZeroZero => 
      apply EvalBig.bigIsZeroZero
      constructor
    case evalIsZeroSucc t₂ ht₂ => 
      apply EvalBig.bigIsZeroSucc (Term.Succ t₂) t₂ 
      case _ => 
        constructor
      case _ => exact ht₂ 
    case evalIsZeroCong => 
      cases h
      case valueNum h => cases h
        
 
  lemma eval_big_trans: ∀ (t₁ t₂ t₃ : Term) (h: Value t₃), Eval t₁ t₂ → EvalBig t₂ t₃ h → EvalBig t₁ t₃ h := by 
    intro t₁ t₂ t₃ h h₁₂ h₂₃ 
    induction h₁₂ generalizing t₃ 
    case evalIfTrue thent elset => 
      apply EvalBig.bigIfTrue 
      case _ => 
        constructor
      case _ => exact h₂₃ 
    case evalIfFalse =>
      apply EvalBig.bigIfFalse 
      case _ => 
        constructor
      case _ => exact h₂₃ 
    case evalIfCong cond₁ cond₂ thent elset h_cond h_ind => 
      cases h₂₃ 
      case bigVal h_val =>
        cases h_val 
        case valueNum h => cases h
      case bigIfTrue h_cond₂ h_then =>
        have h₂ := h_ind Term.Tru (by constructor) h_cond₂ 
        apply EvalBig.bigIfTrue
        case _ => exact h₂ 
        case _ => exact h_then
      case bigIfFalse h_cond₂ h_else =>
        have h₂ := h_ind Term.Fls (by constructor) h_cond₂ 
        apply EvalBig.bigIfFalse 
        case _ => exact h₂ 
        case _ => exact h_else 
    case evalSuccCong  t₄ t₅ h₄₅ h_ind => 
      cases h₂₃ 
      case bigVal h => 
        apply EvalBig.bigSucc 
        case _ => 
          apply h_ind 
          constructor
        case _ => 
          cases h 
          case valueNum h => 
          cases h 
          case valueSucc h => exact h 
      case bigSucc nv hnv h_eval =>
        constructor
        case _ => 
          apply h_ind
          apply h_eval
        case _ => exact hnv
    case evalPredZero =>
      cases h₂₃ 
      case bigVal h =>
        constructor
        constructor
    case evalPredSucc t₄ hnv =>
      cases h₂₃ 
      case bigVal h => 
        constructor
        case _ => constructor
        case _ => exact hnv 
      case bigIfTrue => cases hnv
      case bigIfFalse => cases hnv 
      case bigSucc t₃ nv hnv₂ h_eval => 
        constructor
        case _ => 
          constructor
          case _ => 
            constructor
            case _ => exact h_eval
            case _ => exact hnv₂ 
          case _ => constructor; exact hnv₂ 
        case _ => 
          constructor; exact hnv₂ 
      case bigPredZero => cases hnv
      case bigPredSucc => cases hnv
      case bigIsZeroZero => cases hnv
      case bigIsZeroSucc => cases hnv   
    case evalPredCong t₄ h_eval h_ind => 
      cases h₂₃ 
      case bigVal h => cases h; case valueNum h => cases h
      case bigPredZero t₅ h_eval₂ =>
        constructor
        apply h_ind 
        exact h_eval₂ 
      case bigPredSucc t₅ h_nv h_eval₃ =>
        constructor 
        case _ => 
          apply h_ind 
          exact h_eval₃ 
        case _ => exact h_nv
    case evalIsZeroZero =>
      cases h₂₃ 
      case bigVal h =>
        constructor
        constructor
    case evalIsZeroSucc => 
      cases h₂₃ 
      case bigVal t₃ hnv hv =>
        apply EvalBig.bigIsZeroSucc _ t₃ 
        case _ => constructor
        case _ => exact hnv
    case evalIsZeroCong t₄ t₅ h₄₅ h_ind =>
      cases h₂₃ 
      case bigVal h => 
        cases h; case valueNum h => cases h 
      case bigIsZeroZero h =>
        constructor
        apply h_ind 
        exact h 
      case bigIsZeroSucc nv hnv h_eval => 
        apply EvalBig.bigIsZeroSucc _ nv 
        case _ => 
          apply h_ind 
          exact h_eval
        case _ => exact hnv
     
  theorem eval_big_iff_small: ∀ (t v:Term) (h:Value v), EvalStar t v ↔ EvalBig t v h := by 
  intro t v h
  constructor
  case mp => 
    intro h_star
    induction h_star
    case evalSingle t₁ t₂ h₁₂ =>
      apply eval_val_eval_big 
      exact h₁₂
    case evalRefl t₁ => constructor
    case evalTrans t₁ t₂ t₃ h₁₂ h₂₃ h_ind =>
      have h₂ := h_ind h 
      apply eval_big_trans t₁ t₂ t₃ 
      case _ => exact h₁₂ 
      case _ => exact h₂ 
  case mpr =>
    intro h_eval
    induction h_eval
    case bigVal h => apply EvalStar.evalRefl
    case bigIfTrue cond thent elset v h_val h_cond h_then h_cond₂ h_then₂ =>
      apply evalstar_trans (t₂:= Term.IfT Term.Tru thent elset) 
      case _ => 
        apply evalstar_if_cong
        exact h_cond₂ 
      case _ => 
        apply EvalStar.evalTrans (t₂:=thent)
        case _ => constructor
        case _ => exact h_then₂
    case bigIfFalse cond thent elset v h_val h_cond h_else h_cond₂ h_else₂ =>
      apply evalstar_trans (t₂ := Term.IfT Term.Fls thent elset)
      case _ => 
        apply evalstar_if_cong 
        exact h_cond₂ 
      case _ => 
        apply EvalStar.evalTrans (t₂:=elset)
        case _ => constructor
        case _ => exact h_else₂ 
    case bigSucc t₂ v₂ h_val h_big h_star =>
      apply evalstar_succ_cong 
      exact h_star
    case bigPredZero t₁ h_big h_star =>
      apply evalstar_trans (t₂:= Term.Pred Term.Z)
      case _ => 
        apply evalstar_pred_cong
        exact h_star
      case _ => 
        constructor
        constructor
    case bigPredSucc t₁ nv hnv h_big h_star =>
      apply evalstar_trans (t₂:=Term.Pred (Term.Succ nv))
      case _ =>
        apply evalstar_pred_cong 
        exact h_star
      case _ =>
        constructor
        constructor
        exact hnv 
    case bigIsZeroZero t₁ h_big h_star =>
      apply evalstar_trans (t₂:= Term.IsZero Term.Z)
      case _ => 
        apply evalstar_iszero_cong 
        exact h_star
      case _ => 
        constructor
        constructor
    case bigIsZeroSucc t₁ nv hnv h_big h_star =>
      apply evalstar_trans (t₂:=Term.IsZero (Term.Succ nv))
      case _ => 
        apply evalstar_iszero_cong 
        exact h_star
      case _ => 
        constructor
        constructor
        exact hnv 

end UntypedArith
