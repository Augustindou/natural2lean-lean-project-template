import LeanUtils.Div
/- Parity : functions and theorems related to parity -/

namespace Nat
  def even (a : Nat) : Prop := a % 2 = 0
  def odd (a : Nat) : Prop := a % 2 = 1

  theorem even_rewrite {a : Nat} : even a ↔ ∃ (n : Nat), a = 2 * n := 
    Iff.intro
      (by
        intro h
        rw [even, mod_rewrite] at h
        simp_all)
      (by 
        intro h
        have ⟨n, hn⟩ := h
        rw [hn, even, mod_rewrite]
        exact ⟨_, by rfl⟩)
  
  theorem odd_rewrite {a : Nat} : odd a ↔ ∃ (n : Nat), a = 2 * n + 1 :=
    Iff.intro
      (by
        intro h
        rw [odd, mod_rewrite] at h
        simp_all)
      (by 
        intro h
        have ⟨n, hn⟩ := h
        rw [hn, odd, mod_rewrite]
        exact ⟨_, by rfl⟩)

end Nat
