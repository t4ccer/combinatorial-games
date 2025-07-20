import CombinatorialGames.Game.Short

/-- No constraints (transfinite) on game form. You can prove `AnyGame x` with `trivial` -/
def AnyGame (_ : IGame) := True

/-- A game is a Left end if Left has no immediate moves -/
def IsLeftEnd (g : IGame) : Prop := IGame.leftMoves g = ∅

/-- A game is a Right end if Right has no immediate moves -/
def IsRightEnd (g : IGame) : Prop := IGame.rightMoves g = ∅

class HasNeg (A : IGame → Prop) where
  has_neg (g : IGame) (h1 : A g) : A (-g)

instance : HasNeg AnyGame where
  has_neg _ _ := trivial

instance : HasNeg IGame.Short where
  has_neg g _ := IGame.Short.neg g

-- TODO: Move to IGame

/-- A game with no Left and Right options is zero -/
theorem leftEnd_rightEnd_eq_zero {g : IGame} (hl : IsLeftEnd g) (hr : IsRightEnd g) : g = 0 := by
  rw [IGame.zero_def]
  rw [IsLeftEnd] at hl
  rw [IsRightEnd] at hr
  ext
  · simp only [hl, Set.mem_empty_iff_false, IGame.leftMoves_ofSets]
  · simp only [hr, Set.mem_empty_iff_false, IGame.rightMoves_ofSets]

/-- A game with Left options is not zero -/
theorem mem_leftMoves_ne_zero {g gl : IGame} (h1 : gl ∈ g.leftMoves) : g ≠ 0 := by
  intro h2
  simp only [h2, IGame.leftMoves_zero, Set.mem_empty_iff_false] at h1

/-- A game with Right options is not zero -/
theorem mem_rightMoves_ne_zero {g gr : IGame} (h1 : gr ∈ g.rightMoves) : g ≠ 0 := by
  intro h2
  simp only [h2, IGame.rightMoves_zero, Set.mem_empty_iff_false] at h1

/-- A game with Left options is not zero -/
theorem not_leftEnd_ne_zero {g : IGame} (h1 : ¬(IsLeftEnd g)) : g ≠ 0 := by
  intro h2
  simp only [h2, IsLeftEnd, IGame.leftMoves_zero, not_true_eq_false] at h1

/-- A game with Right options is not zero -/
theorem not_rightEnd_ne_zero {g : IGame} (h1 : ¬(IsRightEnd g)) : g ≠ 0 := by
  intro h2
  simp only [h2, IsRightEnd, IGame.rightMoves_zero, not_true_eq_false] at h1

theorem leftEnd_neg_iff_rightEnd {g : IGame} : IsLeftEnd (-g) ↔ IsRightEnd g := by
  constructor
  all_goals
  · intro h1
    simp only [IsLeftEnd, IGame.leftMoves_neg, Set.neg_eq_empty] at *
    exact h1

theorem rightEnd_neg_iff_leftEnd {g : IGame} : IsRightEnd (-g) ↔ IsLeftEnd g := by
  constructor
  all_goals
  · intro h1
    simp only [IsRightEnd, IGame.rightMoves_neg, Set.neg_eq_empty] at *
    exact h1

/-- Non-zero game has either Left or Right options -/
theorem ne_zero_not_leftEnd_or_not_rightEnd {g : IGame} (h1 : g ≠ 0) :
    ¬(IsLeftEnd g) ∨ ¬(IsRightEnd g) := by
  by_contra h2
  simp only [not_or, not_not] at h2
  obtain ⟨h2, h3⟩ := h2
  exact h1 (leftEnd_rightEnd_eq_zero h2 h3)

/-- Sum of Left ends is a Left end -/
theorem add_leftEnd_leftEnd {g h : IGame} (h1 : IsLeftEnd g) (h2 : IsLeftEnd h) :
    IsLeftEnd (g + h) := by
  unfold IsLeftEnd at h1 h2
  simp [h1, h2, IsLeftEnd]

/-- Sum of Right ends is a Right end -/
theorem add_rightEnd_rightEnd {g h : IGame} (h1 : IsRightEnd g) (h2 : IsRightEnd h) :
    IsRightEnd (g + h) := by
  unfold IsRightEnd at h1 h2
  simp [h1, h2, IsRightEnd]
