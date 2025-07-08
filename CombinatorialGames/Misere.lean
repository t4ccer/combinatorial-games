import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Special
import CombinatorialGames.Game.Birthday
import Mathlib.Data.Set.Operations

inductive PlayerOutcome where
  /-- Left wins going first -/
  | L
  /-- Right wins going first -/
  | R

def IsLeftEnd (g : IGame) : Prop := IGame.leftMoves g = ∅

def IsRightEnd (g : IGame) : Prop := IGame.rightMoves g = ∅

mutual

def LeftWinsGoingFirst (g : IGame) : Prop :=
  IGame.leftMoves g = ∅ ∨ ¬(∀ gl ∈ g.leftMoves, RightWinsGoingFirst gl)
termination_by g
decreasing_by igame_wf

def RightWinsGoingFirst (g : IGame) : Prop :=
  IGame.rightMoves g = ∅ ∨ ¬(∀ gr ∈ g.rightMoves, LeftWinsGoingFirst gr)
termination_by g
decreasing_by igame_wf

end

theorem LeftWinsGoingFirst_def {g : IGame}
    : LeftWinsGoingFirst g ↔ (IsLeftEnd g ∨ (∃ gl ∈ g.leftMoves, ¬RightWinsGoingFirst gl)) := by
  constructor <;> intro h1
  · simp only [LeftWinsGoingFirst, not_forall] at h1
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mp h2)
  · unfold LeftWinsGoingFirst
    simp only [not_forall]
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mpr h2)

theorem RightWinsGoingFirst_def {g : IGame}
    : RightWinsGoingFirst g ↔ (IsRightEnd g ∨ (∃ gr ∈ g.rightMoves, ¬LeftWinsGoingFirst gr)) := by
  constructor <;> intro h1
  · simp only [RightWinsGoingFirst, not_forall] at h1
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mp h2)
  · unfold RightWinsGoingFirst
    simp only [not_forall]
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mpr h2)

open Classical in
/-- Game outcome if Left goes first -/
noncomputable def LeftOutcome (g : IGame) : PlayerOutcome :=
  if LeftWinsGoingFirst g then PlayerOutcome.L else PlayerOutcome.R

open Classical in
/-- Game outcome if Right goes first -/
noncomputable def RightOutcome (g : IGame) : PlayerOutcome :=
  if RightWinsGoingFirst g then PlayerOutcome.R else PlayerOutcome.L

inductive Outcome where
  /-- Left wins -/
  | L
  /-- Next player wins -/
  | N
  /-- Previous (second) player wins -/
  | P
  /-- Right wins -/
  | R

def Outcome.lt' (lhs rhs : Outcome) : Prop :=
    (lhs ≠ Outcome.L ∧ rhs = Outcome.L) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.N) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.P)

instance : LT Outcome where
  lt := Outcome.lt'

def Outcome.le' (lhs rhs : Outcome) : Prop := (lhs = rhs) ∨ (Outcome.lt' lhs rhs)

instance : LE Outcome where
  le := Outcome.le'

theorem Outcome.le_trans' (a b c : Outcome) (hab : Outcome.le' a b) (hbc : Outcome.le' b c) : Outcome.le' a c := by
  cases a
  all_goals cases b
  all_goals cases c
  all_goals simp [Outcome.le', Outcome.lt'] at *

theorem Outcome.lt_iff_le_not_le' (a b : Outcome) : Outcome.lt' a b ↔ Outcome.le' a b ∧ ¬(Outcome.le' b a) := by
  cases a
  all_goals cases b
  all_goals simp [Outcome.le', Outcome.lt'] at *

instance : Preorder Outcome where
  le_refl _ := Or.symm (Or.inr rfl)
  le_trans := Outcome.le_trans'
  lt_iff_le_not_le := Outcome.lt_iff_le_not_le'

theorem Outcome.le_antisymm' (a b : Outcome) (hab : Outcome.le' a b) (hba : Outcome.le' b a) : a = b := by
  cases a
  all_goals cases b
  all_goals simp [Outcome.le', Outcome.lt'] at *

instance : PartialOrder Outcome where
  le_antisymm := Outcome.le_antisymm'

def PlayerOutcomesToGameOutcome : PlayerOutcome → PlayerOutcome → Outcome
  | PlayerOutcome.L, PlayerOutcome.L => Outcome.L
  | PlayerOutcome.R, PlayerOutcome.R => Outcome.R
  | PlayerOutcome.R, PlayerOutcome.L => Outcome.P
  | PlayerOutcome.L, PlayerOutcome.R => Outcome.N

noncomputable def MisereOutcome : IGame → Outcome :=
  fun g => PlayerOutcomesToGameOutcome (LeftOutcome g) (RightOutcome g)

def MisereEq (A : IGame → Prop) (g h : IGame) : Prop :=
  ∀ (x : IGame), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

/-- `G =m A H` means that G =_A H -/
macro_rules | `($x =m $u $y) => `(MisereEq $u $x $y)

recommended_spelling "eq" for "=m" in [MisereEq]

def MisereGe (A : IGame → Prop) (g h : IGame) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))

/-- `G ≥m A H` means that G ≥_A H -/
macro_rules | `($x ≥m $u $y) => `(MisereGe $u $x $y)

recommended_spelling "ge" for "≥m" in [MisereGe]

/-- No constraints on game form. You can prove `AnyGame x` with `trivial` -/
def AnyGame (_ : IGame) := True

theorem Outcome.ge_R (o : Outcome) : o ≥ Outcome.R := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o
  all_goals simp [instLEOutcome, Outcome.le', Outcome.lt']

theorem Outcome.L_ge (o : Outcome) : Outcome.L ≥ o := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o
  all_goals simp [instLEOutcome, Outcome.le', Outcome.lt']

theorem Outcome.ge_P_ge_N_eq_L {o : Outcome} (hp : o ≥ Outcome.P) (hn : o ≥ Outcome.N) : o = Outcome.L := by
  cases o
  all_goals simp [Outcome.le', Outcome.lt', hp, hn, LE.le] at *

theorem leftEnd_rightEnd_eq_zero {g : IGame} (hl : IsLeftEnd g) (hr : IsRightEnd g) : g = 0 := by
  rw [IGame.zero_def]
  rw [IsLeftEnd] at hl
  rw [IsRightEnd] at hr
  ext
  · simp only [hl, Set.mem_empty_iff_false, IGame.leftMoves_ofSets]
  · simp only [hr, Set.mem_empty_iff_false, IGame.rightMoves_ofSets]

theorem proposition6_1 (g h : IGame) :
  (g ≥m AnyGame h) ↔ (∀ (x : IGame),
  (MisereOutcome (h + x) ≥ Outcome.P → MisereOutcome (g + x) ≥ Outcome.P) ∧
  (MisereOutcome (h + x) ≥ Outcome.N → MisereOutcome (g + x) ≥ Outcome.N)) := by
  constructor <;> intro h1
  · -- => is immediate
    intro x
    unfold MisereGe at h1
    constructor <;> intro h2
    · exact Preorder.le_trans Outcome.P (MisereOutcome (h + x)) (MisereOutcome (g + x)) h2 (h1 x trivial)
    · exact Preorder.le_trans Outcome.N (MisereOutcome (h + x)) (MisereOutcome (g + x)) h2 (h1 x trivial)
  · -- For the converse, we must show that o(G + X) > o(H + X), for all X.
    unfold MisereGe
    intro x _
    obtain ⟨h2, h3⟩ := h1 x
    cases ho : MisereOutcome (h + x) with
    | R =>
      -- If o(H + X) = R, then there is nothing to prove
      exact Outcome.ge_R (MisereOutcome (g + x))
    | N =>
      -- If o(H + X) = P or N, it is immediate from (i) or (ii)
      rw [ho] at h3
      exact h3 (Preorder.le_refl Outcome.N)
    | P =>
      rw [ho] at h2
      exact h2 (Preorder.le_refl Outcome.P)
    | L =>
      -- Finally, if o(H + X) = L, then by (i) and (ii) we have o(G + X) > both P and N,
      -- whence o(G + X) = L.
      rw [ho] at h2 h3
      have h4 := h2 (Outcome.L_ge Outcome.P)
      have h5 := h3 (Outcome.L_ge Outcome.N)
      have h6 := Outcome.ge_P_ge_N_eq_L h4 h5
      exact le_of_eq (Eq.symm h6)

open Classical in
noncomputable def Adjoint (g : IGame) : IGame :=
  if g = (0 : IGame) then ⋆
  else if IsLeftEnd g then {Set.range fun gr : g.rightMoves => Adjoint gr|{0}}ᴵ
  else if IsRightEnd g then {{0}|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
  else {Set.range fun gr : g.rightMoves => Adjoint gr|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
termination_by g
decreasing_by igame_wf

notation g"°" => Adjoint g

theorem adjont_zero_eq_star : 0° = ⋆ := by
  unfold Adjoint
  simp only [reduceIte]

theorem adjoint_not_rightEnd (g : IGame) : ¬(IsRightEnd (g°)) := by
  unfold Adjoint IsRightEnd
  by_cases h1 : g = 0 <;> simp [h1]
  by_cases h2 : g.leftMoves = ∅ <;> simp [IsLeftEnd, h2]
  by_cases h3 : g.rightMoves = ∅ <;> simp [h3, h2]

theorem adjoint_not_leftEnd (g : IGame) : ¬(IsLeftEnd (g°)) := by
  unfold Adjoint
  unfold IsLeftEnd
  by_cases h1 : g = 0 <;> simp [h1, IsLeftEnd, IsRightEnd]
  by_cases h2 : g.leftMoves = ∅ <;> by_cases h3 : g.rightMoves = ∅ <;> simp [IsLeftEnd, h2, h3]
  exact h1 (leftEnd_rightEnd_eq_zero h2 h3)

theorem leftEnd_leftWinsGoingFirst {g : IGame} (h1 : IsLeftEnd g) : LeftWinsGoingFirst g := by
  unfold LeftWinsGoingFirst
  exact Or.symm (Or.inr h1)

theorem rightEnd_rightWinsGoingFirst {g : IGame} (h : IsRightEnd g) : RightWinsGoingFirst g := by
  unfold RightWinsGoingFirst
  exact Or.symm (Or.inr h)

theorem ne_zero_not_leftEnd_or_not_rightEnd {g : IGame} (h1 : g ≠ 0) : ¬(IsLeftEnd g) ∨ ¬(IsRightEnd g) := by
  by_contra h2
  simp only [ne_eq, not_or, not_not] at h2
  obtain ⟨h2, h3⟩ := h2
  exact h1 (leftEnd_rightEnd_eq_zero h2 h3)

theorem not_MisereEq_of_not_MisereGe {g h : IGame} (h1 : ¬(g ≥m AnyGame h)) : ¬(g =m AnyGame h) := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨_, h1⟩⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  use trivial
  exact Ne.symm (ne_of_not_le h1)

/-- `o(G) ≥ P` is equivalent to "Left can win playing second on `G`" -/
theorem not_rightWinsGoingFirst_ge_P {g : IGame} (h1 : ¬RightWinsGoingFirst g) : MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome RightOutcome
  cases h2 : LeftOutcome g
  all_goals simp [h1, h2, Outcome.L_ge]

theorem not_leftWinsGoingFirst_le_P {g : IGame} (h1 : ¬LeftWinsGoingFirst g) : MisereOutcome g ≤ Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome
  cases h2 : LeftOutcome g <;> cases h3 : RightOutcome g
  all_goals simp [h1, h2, h3, Outcome.ge_R]

theorem outcome_eq_P_leftWinsGoingFirst {g gl : IGame} (h1 : gl ∈ g.leftMoves) (h2 : MisereOutcome gl = Outcome.P)
    : LeftWinsGoingFirst g := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome RightOutcome at h2
  by_cases h3 : LeftWinsGoingFirst gl <;> by_cases h4 : RightWinsGoingFirst gl <;> simp [h3, h4] at h2
  rw [LeftWinsGoingFirst_def]
  exact Or.inr (by use gl)

theorem outcome_eq_P_rightWinsGoingFirst {g gr : IGame} (h1 : gr ∈ g.rightMoves) (h2 : MisereOutcome gr = Outcome.P)
    : RightWinsGoingFirst g := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome RightOutcome at h2
  by_cases h3 : RightWinsGoingFirst gr <;> by_cases h4 : LeftWinsGoingFirst gr <;> simp [h3, h4] at h2
  rw [RightWinsGoingFirst_def]
  exact Or.inr (by use gr)

theorem add_leftEnd_leftEnd {g h : IGame} (h1 : IsLeftEnd g) (h2 : IsLeftEnd h) : IsLeftEnd (g + h) := by
  unfold IsLeftEnd at h1 h2
  simp [h1, h2, IsLeftEnd]

theorem add_rightEnd_rightEnd {g h : IGame} (h1 : IsRightEnd g) (h2 : IsRightEnd h) : IsRightEnd (g + h) := by
  unfold IsRightEnd at h1 h2
  simp [h1, h2, IsRightEnd]

theorem add_leftEnd_LeftWinsGoingFirst {g h : IGame} (h1 : IsLeftEnd g) (h2 : IsLeftEnd h) : LeftWinsGoingFirst (g + h) :=
  leftEnd_leftWinsGoingFirst (add_leftEnd_leftEnd h1 h2)

theorem add_rightEnd_RightWinsGoingFirst {g h : IGame} (h1 : IsRightEnd g) (h2 : IsRightEnd h) : RightWinsGoingFirst (g + h) :=
  rightEnd_rightWinsGoingFirst (add_rightEnd_rightEnd h1 h2)

theorem rightWinsGoingFirst_outcome_le_N {g : IGame} (h1 : RightWinsGoingFirst g) : MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome RightOutcome
  cases h2 : LeftOutcome g
  all_goals simp [h1, h2, Outcome.L_ge, Outcome.ge_R]

theorem leftWinsGoingFirst_outcome_ge_N {g : IGame} (h1 : LeftWinsGoingFirst g) : MisereOutcome g ≥ Outcome.N := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome
  cases h2 : RightOutcome g
  all_goals simp [h1, h2, Outcome.L_ge, Outcome.ge_R]

theorem outcome_eq_P_not_leftWinsGoingFirst {g : IGame} (h1 : MisereOutcome g = Outcome.P) : ¬LeftWinsGoingFirst g := by
  intro h2
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome at h1
  cases h3 : RightOutcome g <;> simp only [h2, h3, reduceIte, reduceCtorEq] at h1

theorem outcome_eq_P_not_rightWinsGoingFirst {g : IGame} (h1 : MisereOutcome g = Outcome.P) : ¬RightWinsGoingFirst g := by
  intro h2
  unfold MisereOutcome PlayerOutcomesToGameOutcome RightOutcome at h1
  cases h3 : LeftOutcome g <;> simp only [h2, h3, reduceIte, reduceCtorEq] at h1

theorem mem_leftMoves_ne_zero {g gl : IGame} (h1 : gl ∈ g.leftMoves) : g ≠ 0 := by
  intro h2
  simp [h2] at h1

theorem mem_rightMoves_ne_zero {g gr : IGame} (h1 : gr ∈ g.rightMoves) : g ≠ 0 := by
  intro h2
  simp [h2] at h1

theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : IGame} (h1 : gl ∈ g.leftMoves) : gl° ∈ (g°).rightMoves := by
  rw [Adjoint, IsLeftEnd, IsRightEnd]
  have h2 : g ≠ 0 := mem_leftMoves_ne_zero h1
  by_cases h3 : g.leftMoves = ∅ <;> by_cases h4 : g.rightMoves = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : IGame} (h1 : gr ∈ g.rightMoves) : gr° ∈ (g°).leftMoves := by
  rw [Adjoint, IsLeftEnd, IsRightEnd]
  have h2 : g ≠ 0 := mem_rightMoves_ne_zero h1
  by_cases h3 : g.leftMoves = ∅ <;> by_cases h4 : g.rightMoves = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem not_leftEnd_ne_zero {g : IGame} (h1 : ¬(IsLeftEnd g)) : g ≠ 0 := by
  intro h2
  simp only [h2, IsLeftEnd, IGame.leftMoves_zero, not_true_eq_false] at h1

theorem not_rightEnd_ne_zero {g : IGame} (h1 : ¬(IsRightEnd g)) : g ≠ 0 := by
  intro h2
  simp only [h2, IsRightEnd, IGame.rightMoves_zero, not_true_eq_false] at h1

theorem mem_rightMoves_adjoint_exists_leftMoves {g gr : IGame}
  (h1 : gr ∈ g°.rightMoves) (h2 : ¬(IsLeftEnd g))
    : ∃ gl ∈ g.leftMoves, gr = gl° := by
  unfold Adjoint IsLeftEnd IsRightEnd at h1
  unfold IsLeftEnd at h2
  have h3 : g ≠ 0 := not_leftEnd_ne_zero h2
  by_cases h4 : g.rightMoves = ∅
  all_goals
  · simp only [h2, h3, h4, reduceIte, IGame.rightMoves_ofSets, Set.mem_range, Subtype.exists,
               exists_prop] at h1
    obtain ⟨x, h3, h4⟩ := h1
    use x
    apply And.intro h3
    exact Eq.symm h4

theorem mem_leftMoves_adjoint_exists_rightMoves {g gl : IGame}
  (h1 : gl ∈ g°.leftMoves) (h2 : ¬(IsRightEnd g))
    : ∃ gr ∈ g.rightMoves, gl = gr° := by
  unfold Adjoint IsLeftEnd IsRightEnd at h1
  unfold IsRightEnd at h2
  have h3 : g ≠ 0 := not_rightEnd_ne_zero h2
  by_cases h4 : g.leftMoves = ∅
  all_goals
  · simp only [h2, h3, h4, reduceIte, IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists,
          exists_prop] at h1
    obtain ⟨x, h3, h4⟩ := h1
    use x
    apply And.intro h3
    exact Eq.symm h4

theorem mem_adjoint_rightMoves_leftEnd_eq_zero {g gr : IGame} (h1 : gr ∈ g°.rightMoves) (h2 : IsLeftEnd g) : gr = 0 := by
  unfold Adjoint at h1
  unfold IsLeftEnd at h2
  by_cases h3 : g.rightMoves = ∅
  · have h4 : g = 0 := leftEnd_rightEnd_eq_zero h2 h3
    simp only [h4, reduceIte, IGame.rightMoves_star, Set.mem_singleton_iff] at h1
    exact h1
  · have h4 : g ≠ 0 := by
      intro h6
      simp only [h6, IGame.rightMoves_zero, not_true_eq_false] at h3
    simp only [h4, reduceIte, IsLeftEnd, h2, IGame.rightMoves_ofSets, Set.mem_singleton_iff] at h1
    exact h1

theorem mem_adjoint_leftMoves_rightEnd_eq_zero {g gl : IGame} (h1 : gl ∈ g°.leftMoves) (h2 : IsRightEnd g) : gl = 0 := by
  unfold Adjoint at h1
  unfold IsRightEnd at h2
  by_cases h3 : g.leftMoves = ∅
  · have h4 : g = 0 := leftEnd_rightEnd_eq_zero h3 h2
    simp only [h4, reduceIte, IGame.leftMoves_star, Set.mem_singleton_iff] at h1
    exact h1
  · have h4 : g ≠ 0 := by
      intro h6
      simp only [h6, IGame.leftMoves_zero, not_true_eq_false] at h3
    simp only [h2, h3, h4, reduceIte, IsLeftEnd, IsRightEnd, IGame.leftMoves_ofSets, Set.mem_singleton_iff] at h1
    exact h1

theorem outcome_add_adjoint_eq_P (g : IGame) : MisereOutcome (g + g°) = Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome
  -- By symmetry, it suffices to show that Left can win G + G° playing second
  have h1 : RightOutcome (g + Adjoint g) = PlayerOutcome.L := by
    unfold RightOutcome
    have h1 : ¬(RightWinsGoingFirst (g + g°)) := by
      rw [RightWinsGoingFirst_def]
      simp only [IGame.rightMoves_add, Set.mem_union, Set.mem_image, not_or, not_exists, not_and, not_not]
      constructor
      · -- Now G + G° cannot be a Right end, since the definition of
        -- G° ensures that it has at least one Right option
        intro h1
        unfold IsRightEnd at h1
        simp only [IGame.rightMoves_add, Set.union_empty_iff, Set.image_eq_empty] at h1
        exact (adjoint_not_rightEnd g) h1.right
      · intro k h1
        -- So it suffices to show that Left has a winning response to every move by Right.
        apply Or.elim h1 <;> intro ⟨gr, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
        · have h3 : gr + gr° ∈ (gr + g°).leftMoves :=
            IGame.add_left_mem_leftMoves_add (mem_rightMoves_mem_adjoint_leftMoves h2) gr
          rw [LeftWinsGoingFirst_def]
          apply Or.inr
          use gr + gr°
          exact And.intro h3 (outcome_eq_P_not_rightWinsGoingFirst (outcome_add_adjoint_eq_P gr))
        · rw [LeftWinsGoingFirst_def]
          by_cases h3 : g.leftMoves = ∅
          · apply Or.inl
            have h4 : gr = 0 := mem_adjoint_rightMoves_leftEnd_eq_zero h2 h3
            simp only [h4, add_zero]
            exact h3
          · apply Or.inr
            have ⟨gl, h3, h4⟩ := mem_rightMoves_adjoint_exists_leftMoves h2 h3
            rw [h4]
            use gl + gl°
            exact And.intro
              (IGame.add_right_mem_leftMoves_add h3 (gl°))
              (outcome_eq_P_not_rightWinsGoingFirst (outcome_add_adjoint_eq_P gl))
    simp only [h1, reduceIte]

  -- "By symmetry" part
  have h2 : LeftOutcome (g + g°) = PlayerOutcome.R := by
    unfold LeftOutcome
    have h2 : ¬(LeftWinsGoingFirst (g + g°)) := by
      rw [LeftWinsGoingFirst_def]
      simp only [IGame.leftMoves_add, Set.mem_union, Set.mem_image, not_or, not_exists, not_and, not_not]
      constructor
      · intro h1
        unfold IsLeftEnd at h1
        simp only [IGame.leftMoves_add, Set.union_empty_iff, Set.image_eq_empty] at h1
        exact (adjoint_not_leftEnd g) h1.right
      · intro k h1
        apply Or.elim h1 <;> intro ⟨gl, h2, h3⟩ <;> rw [<-h3] <;> clear h1 h3 k
        · have h3 : gl + gl° ∈ (gl + g°).rightMoves :=
            IGame.add_left_mem_rightMoves_add (mem_leftMoves_mem_adjoint_rightMoves h2) gl
          rw [RightWinsGoingFirst_def]
          apply Or.inr
          use gl + gl°
          exact And.intro h3 (outcome_eq_P_not_leftWinsGoingFirst (outcome_add_adjoint_eq_P gl))
        · rw [RightWinsGoingFirst_def]
          by_cases h3 : g.rightMoves = ∅
          · apply Or.inl
            have h4 : gl = 0 := mem_adjoint_leftMoves_rightEnd_eq_zero h2 h3
            simp only [h4, add_zero]
            exact h3
          · apply Or.inr
            have ⟨gr, h3, h4⟩ := mem_leftMoves_adjoint_exists_rightMoves h2 h3
            rw [h4]
            use gr + gr°
            exact And.intro
              (IGame.add_right_mem_rightMoves_add h3 (gr°))
              (outcome_eq_P_not_leftWinsGoingFirst (outcome_add_adjoint_eq_P gr))
    simp only [h2, reduceIte]
  simp only [h1, h2]
termination_by g
decreasing_by all_goals igame_wf

alias proposition6_4 := outcome_add_adjoint_eq_P

def PlayerOutcome.Conjugate : PlayerOutcome → PlayerOutcome
  | .L => .R
  | .R => .L

def Outcome.Conjugate : Outcome → Outcome
  | .L => .R
  | .R => .L
  | .P => .P
  | .N => .N

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

theorem leftOutcome_eq_R_iff_not_leftWinsFirst {g : IGame} : (LeftOutcome g = PlayerOutcome.R) ↔ ¬LeftWinsGoingFirst g := by
  constructor <;> intro h1
  · unfold LeftOutcome at h1
    intro h2
    simp only [h2, reduceIte, reduceCtorEq] at h1
  · unfold LeftOutcome
    simp only [h1, reduceIte]

theorem rightOutcome_eq_L_iff_not_rightWinsFirst {g : IGame} : (RightOutcome g = PlayerOutcome.L) ↔ ¬RightWinsGoingFirst g := by
  constructor <;> intro h1
  · unfold RightOutcome at h1
    intro h2
    simp only [h2, reduceIte, reduceCtorEq] at h1
  · unfold RightOutcome
    simp only [h1, reduceIte]

theorem playerOutcome_eq_iff_conjugate_eq {a b : PlayerOutcome} : (a = b) ↔ (a.Conjugate = b.Conjugate) := by
  cases a <;> cases b <;> simp only [reduceCtorEq, PlayerOutcome.Conjugate]

theorem neg_leftWinsFirst_iff_rightWinsFirst (g : IGame) : (LeftWinsGoingFirst (-g)) ↔ (RightWinsGoingFirst g) := by
  constructor <;> intro h1
  · rw [LeftWinsGoingFirst_def] at h1
    apply Or.elim h1 <;> intro h1
    · apply rightEnd_rightWinsGoingFirst
      exact leftEnd_neg_iff_rightEnd.mp h1
    · obtain ⟨gl, h1, h2⟩ := h1
      rw [RightWinsGoingFirst_def]
      apply Or.inr
      use -gl
      simp only [IGame.leftMoves_neg, Set.mem_neg] at h1
      apply And.intro h1
      exact (neg_leftWinsFirst_iff_rightWinsFirst gl).not.mpr h2
  · rw [RightWinsGoingFirst_def] at h1
    apply Or.elim h1 <;> intro h1
    · apply leftEnd_leftWinsGoingFirst
      rw [leftEnd_neg_iff_rightEnd]
      exact h1
    · obtain ⟨gr, h1, h2⟩ := h1
      rw [LeftWinsGoingFirst_def]
      apply Or.inr
      use -gr
      simp only [IGame.leftMoves_neg, Set.mem_neg, neg_neg]
      apply And.intro h1
      have h3 := (neg_leftWinsFirst_iff_rightWinsFirst (-gr)).not.mp
      simp only [neg_neg] at h3
      exact h3 h2
termination_by IGame.birthday g
decreasing_by
  · simp only [IGame.leftMoves_neg, Set.mem_neg] at h1
    rw [IGame.lt_birthday_iff]
    apply Or.inr
    use -gl
    apply And.intro h1
    rw [IGame.birthday_neg]
  · rw [IGame.birthday_neg, IGame.lt_birthday_iff]
    apply Or.inr
    use gr

mutual

theorem leftOutcome_neg_eq_rightOutcome_conjugate (g : IGame) : LeftOutcome (-g) = (RightOutcome g).Conjugate := by
  unfold LeftOutcome
  rw [LeftWinsGoingFirst_def, IGame.leftMoves_neg]
  split_ifs with h1
  · apply Or.elim h1 <;> intro h1
    · have h2 : IsRightEnd g := leftEnd_neg_iff_rightEnd.mp h1
      unfold RightOutcome
      rw [RightWinsGoingFirst_def]
      simp only [h2, true_or, reduceIte]
      rfl
    · obtain ⟨gl, h1, h2⟩ := h1
      unfold RightOutcome
      have h3 : RightWinsGoingFirst g := by
        rw [RightWinsGoingFirst_def]
        apply Or.inr
        use -gl
        apply And.intro h1
        rw [<-rightOutcome_eq_L_iff_not_rightWinsFirst] at h2
        rw [<-leftOutcome_eq_R_iff_not_leftWinsFirst]
        apply Eq.symm
        have h3 : PlayerOutcome.R.Conjugate = PlayerOutcome.L  := rfl
        rw [playerOutcome_eq_iff_conjugate_eq, h3, <-h2]
        have h4 := rightOutcome_neg_eq_leftOutcome_conjugate (-gl)
        rw [neg_neg] at h4
        exact h4
      simp only [h3, reduceIte]
      rfl
  · simp only [Set.mem_neg, not_or, not_exists, not_and, not_not] at h1
    obtain ⟨h1, h2⟩ := h1
    unfold RightOutcome
    have h3 : ¬RightWinsGoingFirst g := by
      unfold RightWinsGoingFirst
      simp only [not_forall, Classical.not_imp, not_or, not_exists, not_and, not_not]
      have h3 : ¬IsRightEnd g := by
        intro h3
        unfold IsLeftEnd at h1
        simp only [IGame.leftMoves_neg, Set.neg_eq_empty] at h1
        exact h1 h3
      apply And.intro h3
      intro gl h4
      have h5 := h2 (-gl)
      rw [neg_neg] at h5
      have h6 := h5 h4
      rw [RightWinsGoingFirst_def] at h6
      apply Or.elim h6 <;> intro h6
      · rw [LeftWinsGoingFirst_def]
        apply Or.inl
        unfold IsRightEnd at h6
        simp only [IGame.rightMoves_neg, Set.neg_eq_empty] at h6
        exact h6
      · obtain ⟨x, h6, h7⟩ := h6
        simp only [IGame.rightMoves_neg, Set.mem_neg] at h6
        rw [LeftWinsGoingFirst_def]
        apply Or.inr
        use -x
        apply And.intro h6
        have h8 : ¬LeftWinsGoingFirst (- (-x)) := by
          simp only [neg_neg]
          exact h7
        exact (neg_leftWinsFirst_iff_rightWinsFirst (-x)).not.mp h8
    simp only [h3, reduceIte]
    rfl
termination_by g
decreasing_by igame_wf

theorem rightOutcome_neg_eq_leftOutcome_conjugate (g : IGame) : RightOutcome (-g) = (LeftOutcome g).Conjugate := by
  unfold RightOutcome
  rw [RightWinsGoingFirst_def, IGame.rightMoves_neg]
  split_ifs with h1
  · apply Or.elim h1 <;> intro h1
    · have h2 : IsLeftEnd g := rightEnd_neg_iff_leftEnd.mp h1
      unfold LeftOutcome
      rw [LeftWinsGoingFirst_def]
      simp only [h2, true_or, reduceIte]
      rfl
    · obtain ⟨gr, h1, h2⟩ := h1
      unfold LeftOutcome
      have h3 : LeftWinsGoingFirst g := by
        rw [LeftWinsGoingFirst_def]
        apply Or.inr
        use -gr
        apply And.intro h1
        rw [<-leftOutcome_eq_R_iff_not_leftWinsFirst] at h2
        rw [<-rightOutcome_eq_L_iff_not_rightWinsFirst]
        apply Eq.symm
        have h3 : PlayerOutcome.L.Conjugate = PlayerOutcome.R  := rfl
        rw [playerOutcome_eq_iff_conjugate_eq, h3, <-h2]
        have h4 := leftOutcome_neg_eq_rightOutcome_conjugate (-gr)
        rw [neg_neg] at h4
        exact h4
      simp only [h3, reduceIte]
      rfl
  · simp only [Set.mem_neg, not_or, not_exists, not_and, not_not] at h1
    obtain ⟨h1, h2⟩ := h1
    unfold LeftOutcome
    have h3 : ¬LeftWinsGoingFirst g := by
      unfold LeftWinsGoingFirst
      simp only [not_forall, Classical.not_imp, not_or, not_exists, not_and, not_not]
      have h3 : ¬IsLeftEnd g := by
        intro h3
        unfold IsRightEnd at h1
        simp only [IGame.rightMoves_neg, Set.neg_eq_empty] at h1
        exact h1 h3
      apply And.intro h3
      intro gl h4
      have h5 := h2 (-gl)
      rw [neg_neg] at h5
      have h6 := h5 h4
      rw [LeftWinsGoingFirst_def] at h6
      apply Or.elim h6 <;> intro h6
      · rw [RightWinsGoingFirst_def]
        apply Or.inl
        unfold IsLeftEnd at h6
        simp only [IGame.leftMoves_neg, Set.neg_eq_empty] at h6
        exact h6
      · obtain ⟨x, h6, h7⟩ := h6
        simp only [IGame.leftMoves_neg, Set.mem_neg] at h6
        rw [RightWinsGoingFirst_def]
        apply Or.inr
        use -x
        apply And.intro h6
        exact (neg_leftWinsFirst_iff_rightWinsFirst x).not.mpr h7
    simp only [h3, reduceIte]
    rfl
termination_by g
decreasing_by igame_wf

end

theorem conjugate_of_conjugates {g : IGame}
    : PlayerOutcomesToGameOutcome (RightOutcome g).Conjugate (LeftOutcome g).Conjugate
      = (MisereOutcome g).Conjugate := by
  cases h1 : RightOutcome g <;> cases h2 : LeftOutcome g
  all_goals simp only [h1, h2, PlayerOutcomesToGameOutcome, PlayerOutcome.Conjugate,
                       Outcome.Conjugate, MisereOutcome]

theorem outcome_conjugate_eq_outcome_neg {g : IGame} : (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [rightOutcome_neg_eq_leftOutcome_conjugate, leftOutcome_neg_eq_rightOutcome_conjugate, conjugate_of_conjugates, h1]
    rfl

theorem outcome_ge_conjugate_le {g h : IGame} (h1 : MisereOutcome g ≥ MisereOutcome h) :
    (MisereOutcome g).Conjugate ≤ (MisereOutcome h).Conjugate := by
  cases h2 : MisereOutcome g
    <;> cases h3 : MisereOutcome h
    <;> unfold Outcome.Conjugate
    <;> simp [h1, h2, h3, instLEOutcome, Outcome.le', Outcome.lt']
    <;> simp [h2, h3] at h1
    <;> absurd h1
    <;> simp [instLEOutcome, Outcome.le', Outcome.lt']

theorem conjugate_conjugate_eq_self {o : Outcome} : o.Conjugate.Conjugate = o := by
  unfold Outcome.Conjugate
  cases o <;> rfl

theorem not_ge_neg_iff.aux {g h : IGame} (h1 : g ≥m AnyGame h): (-h) ≥m AnyGame (-g) := by
  unfold MisereGe at *
  intro x _
  have h2 := h1 (-x)
  have h3 := outcome_ge_conjugate_le (h2 trivial)
  have h4 : MisereOutcome (-h + x) = (MisereOutcome (-h + x)).Conjugate.Conjugate := Eq.symm conjugate_conjugate_eq_self
  have h5 : (MisereOutcome (-h + x)).Conjugate.Conjugate = (MisereOutcome (h + (-x))).Conjugate := by
    simp only [outcome_conjugate_eq_outcome_neg, neg_add_rev, neg_neg, add_comm]
  rw [h4, h5]
  have h6 : (MisereOutcome (g + (-x))).Conjugate = MisereOutcome (-g + x) := by
    simp only [outcome_conjugate_eq_outcome_neg, neg_add_rev, neg_neg, add_comm]
  rw [<-h6]
  apply outcome_ge_conjugate_le
  exact h2 trivial

theorem neg_ge_neg_iff {g h : IGame} : ((-h) ≥m AnyGame (-g) ↔ g ≥m AnyGame h) := by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp only [neg_neg] at h2
    exact h2
  · exact not_ge_neg_iff.aux h1

theorem leftEnd_not_leftEnd_not_ge {g h : IGame} (h1 : IsLeftEnd h) (h2 : ¬(IsLeftEnd g)) : ¬(g ≥m AnyGame h) := by
  let t := {Set.range fun hr : h.rightMoves => Adjoint hr | { {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ } }ᴵ
  -- First consider H + T
  have h3 : MisereOutcome (h + t) ≥ Outcome.P := by
    apply not_rightWinsGoingFirst_ge_P
    unfold RightWinsGoingFirst
    simp only [IGame.rightMoves_add, Set.union_empty_iff, Set.image_eq_empty, Set.mem_union,
               Set.mem_image, not_or, not_and, not_exists, not_not]
    apply And.intro (fun _ => by
      simp only [t, IGame.rightMoves_ofSets, Set.singleton_ne_empty, not_false_eq_true])
    intro x h3
    apply Or.elim h3 <;> clear h3 <;> intro ⟨hr, h3, h4⟩ <;> rw [<-h4]
    · -- If Right moves to H^R + T, then Left has a winning response to H^R + (H^R)°
      refine outcome_eq_P_leftWinsGoingFirst ?_ (outcome_add_adjoint_eq_P hr)
      refine IGame.add_left_mem_leftMoves_add ?_ hr
      simp only [t, IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop]
      exists hr
    · -- If instead Right moves to H + { | (G^L)°}, then Left wins outright,
      -- since (by the assumption on H) both components are Left ends
      apply add_leftEnd_LeftWinsGoingFirst h1
      simp only [t, IGame.rightMoves_ofSets, Set.mem_singleton_iff] at h3
      simp only [t, h3, IGame.leftMoves_ofSets, IsLeftEnd]
  -- Next consider G + T
  have h4 : MisereOutcome (g + t) ≤ Outcome.N := by
    apply rightWinsGoingFirst_outcome_le_N
    rw [RightWinsGoingFirst_def]
    apply Or.inr
    -- Right has a move to G + { | (G^L)° }
    use (g + {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ)
    constructor
    · refine IGame.add_left_mem_rightMoves_add ?_ g
      simp only [t, IGame.rightMoves_ofSets, Set.mem_singleton_iff]
    · rw [LeftWinsGoingFirst_def]
      simp only [IGame.leftMoves_add, IGame.leftMoves_ofSets, Set.image_empty, Set.union_empty,
                 Set.image_eq_empty, Set.mem_image, exists_exists_and_eq_and, not_or, not_exists,
                 not_and, not_not, IsLeftEnd]
      apply And.intro h2
      intro gl h4
      -- from which Left's only options have the form G^L + { | (G^L)° }
      rw [RightWinsGoingFirst_def]
      apply Or.inr
      -- There must be at least one such option, by the assumption on G;
      -- and each such option has a mirror-image response by Right, to G^L + (G^L)°
      use (gl + gl°)
      refine And.intro ?_ (outcome_eq_P_not_leftWinsGoingFirst (outcome_add_adjoint_eq_P gl))
      refine IGame.add_left_mem_rightMoves_add ?_ gl
      simp only [IGame.rightMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop]
      use gl
  unfold MisereGe
  intro h5
  have h6 : MisereOutcome (g + t) ≥ Outcome.P :=
    Preorder.le_trans Outcome.P (MisereOutcome (h + t)) (MisereOutcome (g + t)) h3 (h5 t trivial)
  cases h7 : MisereOutcome (g + t)
  all_goals simp only [t, h7, Outcome.le', Outcome.lt', and_false, and_self, and_true,
                       ge_iff_le, instLEOutcome, le_refl, ne_eq, not_false_eq_true,
                       not_true_eq_false, or_false, or_self, or_true, reduceCtorEq] at h4 h6

alias theorem6_6 := leftEnd_not_leftEnd_not_ge

theorem rightEnd_not_rightEnd_not_ge {g h : IGame} (h1 : IsRightEnd h) (h2 : ¬(IsRightEnd g)) : ¬(h ≥m AnyGame g) := by
  unfold IsRightEnd at h1 h2
  have h3 : IsLeftEnd (-h) := leftEnd_neg_iff_rightEnd.mpr h1
  have h4 : ¬(IsLeftEnd (-g)) := leftEnd_neg_iff_rightEnd.not.mpr h2
  have h5 : ¬((-g) ≥m AnyGame (-h)) := leftEnd_not_leftEnd_not_ge h3 h4
  exact neg_ge_neg_iff.not.mp h5

theorem MisereEq_symm {A : IGame → Prop} {g h : IGame} (h1 : g =m A h) : h =m A g := by
  unfold MisereEq at *
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

theorem ne_zero_not_eq_zero {g : IGame} (h1 : g ≠ 0) : ¬(g =m AnyGame 0) := by
  apply Or.elim (ne_zero_not_leftEnd_or_not_rightEnd h1) <;> intro h2
  · exact not_MisereEq_of_not_MisereGe (leftEnd_not_leftEnd_not_ge IGame.leftMoves_zero h2)
  · intro h3
    exact (not_MisereEq_of_not_MisereGe (rightEnd_not_rightEnd_not_ge IGame.rightMoves_zero h2)) (MisereEq_symm h3)

alias corollary6_7 := ne_zero_not_eq_zero

theorem eq_zero_iff_identical_zero {g : IGame} : (g =m AnyGame 0 ↔ g = 0) := by
  constructor <;> intro h1
  · by_contra h2
    have h3 := ne_zero_not_eq_zero h2
    exact h3 h1
  · rw [h1]
    intro _
    exact congrFun rfl

theorem MisereGe_antisymm {A : IGame → Prop} {g h : IGame} (h1 : g ≥m A h) (h2 : h ≥m A g) : g =m A h :=
  fun x h3 => PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)
