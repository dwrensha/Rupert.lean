import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/--
Lemma for helping with goals such as
```
  ∀ i : Fin 8, 0 ≤ ![1.4, 3, 5, 2, 0, 1, 1, 0.2]
```
Usually one would do something like `intro i; fin_cases i <;> norm_num` here.
However, `fin_cases` consumes a considerable number of heartbeats, which
can become problematic if this is done many times in a larger proof.

With this lemma, once can instead do

```
apply all_fin_8_vec <;> norm_num
```
-/
lemma all_fin_8_vec {α : Type} {a b c d e f g h : α} (p : α → Prop) :
    p a → p b → p c → p d → p e → p f → p g → p h →
    ∀ ii : Fin 8, p (![a, b, c, d, e, f, g, h] ii) := by
  intro ha hb hc hd he hf hg hh ii
  fin_cases ii <;> simp_all

/-- Analogue of `all_fin_8_vec` for length-20 vectors. -/
lemma all_fin_20_vec {α : Type} {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂
    a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ : α} (p : α → Prop) :
    p a₀ → p a₁ → p a₂ → p a₃ → p a₄ → p a₅ → p a₆ → p a₇ → p a₈ → p a₉ →
    p a₁₀ → p a₁₁ → p a₁₂ → p a₁₃ → p a₁₄ → p a₁₅ → p a₁₆ → p a₁₇ →
    p a₁₈ → p a₁₉ →
    ∀ ii : Fin 20, p (![a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁,
      a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉] ii) := by
  intro h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇
    h₁₈ h₁₉ ii
  fin_cases ii <;> simp_all
