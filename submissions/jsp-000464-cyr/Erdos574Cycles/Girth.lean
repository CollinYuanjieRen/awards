import Erdos574Cycles.Definitions

/-! The incidence structure `D(3, q)` has no 4-cycle and no 6-cycle (girth 8). -/

namespace Erdos574

variable {F : Type*} [Field F]

/-- Two points on a common line with the same first coordinate coincide. -/
theorem point_eq_of_incid {p p' l : F × F × F} (h : Incid F p l) (h' : Incid F p' l)
    (ha : p.1 = p'.1) : p = p' := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := p'
  obtain ⟨x, y, z⟩ := l
  simp only [Incid] at h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have ha' : a = a' := ha
  have hb : b = b' := by linear_combination h1' - h1 - x * ha'
  have hc : c = c' := by linear_combination h2' - h2 - y * ha'
  rw [ha', hb, hc]

/-- Two lines through a common point with the same first coordinate coincide. -/
theorem line_eq_of_incid {p l l' : F × F × F} (h : Incid F p l) (h' : Incid F p l')
    (hx : l.1 = l'.1) : l = l' := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨x, y, z⟩ := l
  obtain ⟨x', y', z'⟩ := l'
  simp only [Incid] at h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hx' : x = x' := hx
  have hy : y = y' := by linear_combination h1 - h1' + a * hx'
  have hz : z = z' := by linear_combination h2 - h2' + a * hy
  rw [hx', hy, hz]

/-- No 4-cycle: two distinct points lie on at most one common line. -/
theorem no_C4 {p p' l l' : F × F × F} (hp : p ≠ p') (hl : l ≠ l')
    (h1 : Incid F p l) (h2 : Incid F p' l) (h3 : Incid F p l') (h4 : Incid F p' l') : False := by
  have hpa : p.1 ≠ p'.1 := fun h => hp (point_eq_of_incid h1 h2 h)
  have hla : l.1 ≠ l'.1 := fun h => hl (line_eq_of_incid h1 h3 h)
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := p'
  obtain ⟨x, y, z⟩ := l
  obtain ⟨x', y', z'⟩ := l'
  simp only [Incid] at h1 h2 h3 h4
  have key : (x - x') * (a' - a) = 0 := by
    linear_combination h1.1 - h2.1 + h4.1 - h3.1
  rcases mul_eq_zero.1 key with h | h
  · exact hla (sub_eq_zero.1 h)
  · exact hpa (sub_eq_zero.1 h).symm

/-- No 6-cycle. -/
theorem no_C6 {p₁ p₂ p₃ l₁ l₂ l₃ : F × F × F}
    (hp12 : p₁ ≠ p₂) (hp23 : p₂ ≠ p₃) (hp13 : p₁ ≠ p₃)
    (hl12 : l₁ ≠ l₂) (hl23 : l₂ ≠ l₃) (hl13 : l₁ ≠ l₃)
    (h11 : Incid F p₁ l₁) (h21 : Incid F p₂ l₁) (h22 : Incid F p₂ l₂) (h32 : Incid F p₃ l₂)
    (h33 : Incid F p₃ l₃) (h13 : Incid F p₁ l₃) : False := by
  have ha12 : p₁.1 ≠ p₂.1 := fun h => hp12 (point_eq_of_incid h11 h21 h)
  have ha23 : p₂.1 ≠ p₃.1 := fun h => hp23 (point_eq_of_incid h22 h32 h)
  have hx12 : l₁.1 ≠ l₂.1 := fun h => hl12 (line_eq_of_incid h21 h22 h)
  obtain ⟨a₁, b₁, c₁⟩ := p₁
  obtain ⟨a₂, b₂, c₂⟩ := p₂
  obtain ⟨a₃, b₃, c₃⟩ := p₃
  obtain ⟨x₁, y₁, z₁⟩ := l₁
  obtain ⟨x₂, y₂, z₂⟩ := l₂
  obtain ⟨x₃, y₃, z₃⟩ := l₃
  simp only [Incid] at h11 h21 h22 h32 h33 h13
  -- the `b`-differences along the three sides of the hexagon
  have hb1 : b₁ - b₂ = x₁ * (a₂ - a₁) := by linear_combination h21.1 - h11.1
  have hb2 : b₂ - b₃ = x₂ * (a₃ - a₂) := by linear_combination h32.1 - h22.1
  have hb3 : b₃ - b₁ = x₃ * (a₁ - a₃) := by linear_combination h13.1 - h33.1
  have hE1 : x₁ * (a₂ - a₁) + x₂ * (a₃ - a₂) + x₃ * (a₁ - a₃) = 0 := by
    linear_combination -hb1 - hb2 - hb3
  -- the `c`-differences along the three sides of the hexagon
  have hc1 : c₁ - c₂ = y₁ * (a₂ - a₁) := by linear_combination h21.2 - h11.2
  have hc2 : c₂ - c₃ = y₂ * (a₃ - a₂) := by linear_combination h32.2 - h22.2
  have hc3 : c₃ - c₁ = y₃ * (a₁ - a₃) := by linear_combination h13.2 - h33.2
  have hE2 : y₁ * (a₂ - a₁) + y₂ * (a₃ - a₂) + y₃ * (a₁ - a₃) = 0 := by
    linear_combination -hc1 - hc2 - hc3
  -- substituting `yᵢ = bᵢ + xᵢ aᵢ` into `hE2` and eliminating `b₂, b₃, x₃`
  have key : (a₂ - a₁) * (a₃ - a₂) * (x₂ - x₁) = 0 := by
    linear_combination hE2 - (a₂ - a₁) * h11.1 - (a₃ - a₂) * h22.1 - (a₁ - a₃) * h33.1
      - (a₂ - a₁) * hb1 + (a₁ - a₃) * hb2 - a₃ * hE1
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact ha12 (sub_eq_zero.1 h').symm
    · exact ha23 (sub_eq_zero.1 h').symm
  · exact hx12 (sub_eq_zero.1 h).symm

end Erdos574
