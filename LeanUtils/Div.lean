import Mathlib.Init.Data.Nat.Basic
import Mathlib.Tactic.Ring


/- Div : functions and theorems relative to the division and modulo operations -/

namespace Nat
  def divisible (b a : Nat) : Prop := a % b = 0

  -- TODO : more general version of this will be easy to implement with access to dec_trivial (currently not yet in mathlib4) -> https://github.com/leanprover-community/mathlib/blob/master/src/tactic/dec_trivial.lean
  theorem mod_3_poss (a : Nat) : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 :=
    -- copied from Mathlib.Init.Data.Nat.Lemmas (and modified from mod_two_eq_zero_or_one)
    match a % 3, @Nat.mod_lt a 3 (by simp) with
    | 0,   _ => Or.inl rfl
    | 1,   _ => Or.inr (Or.inl rfl)
    | 2,   _ => Or.inr (Or.inr rfl)

  -- TODO : find equivalent in mathlib / prove it
  axiom mod_rewrite {a b m : Nat} : a % b = m ↔ ∃ k, a = b * k + m

  
  theorem div_plus_div {a b c : Nat} : divisible c a → divisible c b → divisible c (a + b) := by
    intros h₁ h₂
    rw [divisible, mod_rewrite] at h₁ h₂
    have ⟨n, hn⟩ := h₁
    have ⟨m, hm⟩ := h₂
    rw [hn, hm]
    apply mod_rewrite.mpr
    exact ⟨n+m, by ring⟩

end Nat

