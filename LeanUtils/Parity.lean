import LeanUtils.div
/- Parity : functions and theorems related to parity -/

namespace Nat
  def even (a : Nat) : Prop := ∃ (n : Nat), a = 2 * n
  def odd (a : Nat) : Prop := ∃ (n : Nat), a = 2 * n + 1

  theorem even_rewrite {a : Nat} : even a ↔ a % 2 = 0 := 
    Iff.intro
      (by 
        intro h
        have ⟨n, hn⟩ := h
        rw [hn, mod_rewrite]
        exact ⟨n, by simp⟩)
      (by
        intro h
        rw [even]
        rw [mod_rewrite] at h
        simp_all)
  
  theorem odd_rewrite {a : Nat} : odd a ↔ a % 2 = 1 :=
    Iff.intro
      (by 
        intro h
        have ⟨n, hn⟩ := h
        rw [hn, mod_rewrite]
        exact ⟨n, by simp⟩)
      (by
        intro h
        rw [odd]
        rw [mod_rewrite] at h
        simp_all)

end Nat
