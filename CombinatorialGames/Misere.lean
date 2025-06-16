import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Special
import Mathlib.Data.Set.Operations

inductive PlayerOutcome where
  /-- Left wins going first -/
  | L
  /-- Right wins going first -/
  | R

mutual

def MisereOutcomeL_isL (g : IGame): Prop :=
  IGame.leftMoves g = ∅ ∨ (∃ gl ∈ g.leftMoves, ¬MisereOutcomeR_isR gl)
termination_by g
decreasing_by
  -- TODO: Do something so we can see here that gl ∈ g.leftMoves
  sorry

def MisereOutcomeR_isR (g : IGame) : Prop :=
  IGame.rightMoves g = ∅ ∨ (∃ gr ∈ g.rightMoves, ¬MisereOutcomeL_isL gr)
termination_by g
decreasing_by
  sorry

end

/-- Game outcome if Left goes first -/
noncomputable def MisereOutcomeL (g : IGame) : PlayerOutcome :=
  have _ := Classical.propDecidable (MisereOutcomeL_isL g)
  if MisereOutcomeL_isL g then PlayerOutcome.L else PlayerOutcome.R

/-- Game outcome if Right goes first -/
noncomputable def MisereOutcomeR (g : IGame) : PlayerOutcome :=
  have _ := Classical.propDecidable (MisereOutcomeR_isR g)
  if MisereOutcomeR_isR g then PlayerOutcome.R else PlayerOutcome.L

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

theorem Outcome.le'_trans (a b c : Outcome) (hab : Outcome.le' a b) (hbc : Outcome.le' b c) : Outcome.le' a c := by
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
  le_trans := Outcome.le'_trans
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
  fun g => PlayerOutcomesToGameOutcome (MisereOutcomeL g) (MisereOutcomeR g)

def MisereEq (g h : IGame) : Prop := ∀ (x : IGame), MisereOutcome (g + x) = MisereOutcome (h + x)

def MisereGe (g h : IGame) : Prop := ∀ (x : IGame), MisereOutcome (g + x) ≥ MisereOutcome (h + x)

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

theorem Outcome.ge_PN {o : Outcome} (hp : o ≥ Outcome.P) (hn : o ≥ Outcome.N) : o = Outcome.L := by
  cases o
  all_goals simp [Outcome.le', Outcome.lt', hp, hn, LE.le] at *

theorem proposition6_1 (g h : IGame) :
  MisereGe g h ↔ (∀ (x : IGame),
  (MisereOutcome (h + x) ≥ Outcome.P → MisereOutcome (g + x) ≥ Outcome.P) ∧
  (MisereOutcome (h + x) ≥ Outcome.N → MisereOutcome (g + x) ≥ Outcome.N)) := by
  constructor <;> intro h1
  · -- => is immediate
    intro x
    unfold MisereGe at h1
    constructor <;> intro h2
    · exact Preorder.le_trans Outcome.P (MisereOutcome (h + x)) (MisereOutcome (g + x)) h2 (h1 x)
    · exact Preorder.le_trans Outcome.N (MisereOutcome (h + x)) (MisereOutcome (g + x)) h2 (h1 x)
  · -- For the converse, we must show that o(G + X) > o(H + X), for all X.
    unfold MisereGe
    intro x
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
      rw [ho] at h2
      rw [ho] at h3
      have h4 := h2 (Outcome.L_ge Outcome.P)
      have h5 := h3 (Outcome.L_ge Outcome.N)
      have h6 := Outcome.ge_PN h4 h5
      exact le_of_eq (Eq.symm h6)

noncomputable def Adjoint (g : IGame) : IGame :=
  have _ := Classical.propDecidable (g = 0)
  have _ := Classical.propDecidable (g.leftMoves = ∅)
  have _ := Classical.propDecidable (g.rightMoves = ∅)
  if g = (0 : IGame) then {{⋆}|{⋆}}ᴵ
  else if g.leftMoves = ∅ then {Set.range fun gr : g.rightMoves => Adjoint gr|{0}}ᴵ
  else if g.rightMoves = ∅ then {{0}|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
  else {Set.range fun gr : g.rightMoves => Adjoint gr|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
termination_by g
decreasing_by igame_wf

notation g"°" => Adjoint g

theorem Adjont_zero_def : 0° = {{⋆}|{⋆}}ᴵ := by
  unfold Adjoint
  simp only [reduceIte]

theorem leftEmtpy_rightEmtpy_zero {g : IGame} (hl : g.leftMoves = ∅) (hr : g.rightMoves = ∅) : g = 0 := by
  rw [IGame.zero_def]
  ext
  · simp [hl]
  · simp [hr]

theorem proposition6_4 {g : IGame} : MisereOutcome (g + g°) = Outcome.P := by
  unfold MisereOutcome
  unfold PlayerOutcomesToGameOutcome
  -- FIXME: Comments and code are backwards
  have h1 : MisereOutcomeL (g + g°) = PlayerOutcome.R := by
    unfold MisereOutcomeL
    have h2 : ¬(MisereOutcomeL_isL (g + g°)) := by
      unfold MisereOutcomeL_isL
      simp
      constructor
      · -- Now G + G° cannot be a Right end, since the definition of
        -- G° ensures that it has at least one Right option
        intro h3
        unfold Adjoint
        simp [h3]
        by_cases h5 : g = 0
        · simp [h5]
        · simp [h5]
          intro h6
          exact h5 (leftEmtpy_rightEmtpy_zero h3 h6)
      · intro k h3
        -- So it suffices to show that Left has a winning response to every move by Right.
        -- There are two cases:
        -- If Right moves to G^R + G° or G + (G^L)°, Left has a mirror image move on
        -- the other component, which wins by induction on G.
        apply Or.elim h3
          <;> intro h4
          <;> obtain ⟨gl, ⟨h4, h5⟩⟩ := h4
          <;> rw [<-h5]
        · -- Show that G^L + G° is in R if Right goes first
          sorry
        · -- Show that G + (G°)^L is in R if Right goes first

          sorry
    simp [h2]
  have h2 : MisereOutcomeR (g + Adjoint g) = PlayerOutcome.L := by
    -- TODO: By symmetry
    sorry
  simp [h1, h2]
