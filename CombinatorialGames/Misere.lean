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

open Classical in
/-- Game outcome if Left goes first -/
noncomputable def MisereOutcomeL (g : IGame) : PlayerOutcome :=
  if MisereOutcomeL_isL g then PlayerOutcome.L else PlayerOutcome.R

open Classical in
/-- Game outcome if Right goes first -/
noncomputable def MisereOutcomeR (g : IGame) : PlayerOutcome :=
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
      rw [ho] at h2 h3
      have h4 := h2 (Outcome.L_ge Outcome.P)
      have h5 := h3 (Outcome.L_ge Outcome.N)
      have h6 := Outcome.ge_PN h4 h5
      exact le_of_eq (Eq.symm h6)

open Classical in
noncomputable def Adjoint (g : IGame) : IGame :=
  if g = (0 : IGame) then ⋆
  else if g.leftMoves = ∅ then {Set.range fun gr : g.rightMoves => Adjoint gr|{0}}ᴵ
  else if g.rightMoves = ∅ then {{0}|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
  else {Set.range fun gr : g.rightMoves => Adjoint gr|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
termination_by g
decreasing_by igame_wf

notation g"°" => Adjoint g

theorem Adjont_zero_def : 0° = ⋆ := by
  unfold Adjoint
  simp only [reduceIte]

theorem leftEmtpy_rightEmtpy_zero {g : IGame} (hl : g.leftMoves = ∅) (hr : g.rightMoves = ∅) : g = 0 := by
  rw [IGame.zero_def]
  ext
  · simp only [hl, Set.mem_empty_iff_false, IGame.leftMoves_ofSets]
  · simp only [hr, Set.mem_empty_iff_false, IGame.rightMoves_ofSets]

theorem nonEmpty_Adjoint_right (g : IGame) : g°.rightMoves ≠ ∅ := by
  unfold Adjoint
  by_cases h1 : g = 0 <;> simp [h1]
  by_cases h2 : g.leftMoves = ∅ <;> simp [h2]
  by_cases h3 : g.rightMoves = ∅ <;> simp [h3, h2]

theorem nonEmpty_Adjoint_left (g : IGame) : g°.leftMoves ≠ ∅ := by
  unfold Adjoint
  by_cases h1 : g = 0 <;> simp [h1]
  by_cases h2 : g.leftMoves = ∅ <;> by_cases h3 : g.rightMoves = ∅ <;> simp [h2, h3]
  exact h1 (leftEmtpy_rightEmtpy_zero h2 h3)

theorem rightMoves_of_Adjoint_of_leftEnd {g : IGame} (h : g.leftMoves = ∅) : g°.rightMoves = {0} := by
  unfold Adjoint
  by_cases h1 : g = 0 <;> simp [h, h1]

theorem MisereOutcomeL_isL_of_leftEnd {g : IGame} (h : g.leftMoves = ∅) : MisereOutcomeL_isL g := by
  unfold MisereOutcomeL_isL
  exact Or.symm (Or.inr h)

theorem leftMoves_ne_empty_mem {g : IGame} (h : g.leftMoves ≠ ∅) : ∃gl, (gl ∈ g.leftMoves) :=
  Set.nonempty_iff_ne_empty.mpr h

theorem proposition6_4 (g : IGame) : MisereOutcome (g + g°) = Outcome.P := by
  unfold MisereOutcome
  unfold PlayerOutcomesToGameOutcome
  -- By symmetry, it suffices to show that Left can win G + G° playing second
  have h1 : MisereOutcomeR (g + Adjoint g) = PlayerOutcome.L := by
    unfold MisereOutcomeR
    have h1 : ¬(MisereOutcomeR_isR (g + g°)) := by
      unfold MisereOutcomeR_isR
      simp
      constructor
      · -- Now G + G° cannot be a Right end, since the definition of
        -- G° ensures that it has at least one Right option
        exact fun _ => nonEmpty_Adjoint_right g
      · intro k h1
        -- So it suffices to show that Left has a winning response to every move by Right.
        -- There are two cases:
        by_cases h2 : g.leftMoves = ∅
        · -- If G is a Left end and Right moves to G + 0, then Left has no move and so wins a priori.
          apply Or.elim h1 <;> intro ⟨gr, ⟨h3, h4⟩⟩ <;> rw [<-h4] <;> clear h1 h4 k
          · -- The same recursion as in the other branch of h2 maybe?
            induction g using IGame.moveRecOn with
            | H h h4 h5 =>

              sorry
          · simp [rightMoves_of_Adjoint_of_leftEnd h2] at h3
            rw [h3, add_zero]
            clear h3
            exact MisereOutcomeL_isL_of_leftEnd h2
        · -- If Right moves to G^R + G° or G + (G^L)°, Left has a mirror image move on
          -- the other component, which wins by induction on G.
          induction g using IGame.moveRecOn with
          | H g h6 h7 =>
          apply Or.elim h1
            <;> intro ⟨gr, ⟨h4, h5⟩⟩
            <;> rw [<-h5]
            <;> rw [<-h5] at h6 h7
          · -- Show that G^L + G° is in R if Right goes first
            clear h1 h5 k
            obtain ⟨gl, h8⟩ := leftMoves_ne_empty_mem h2
            sorry
          · -- Show that G + (G°)^L is in R if Right goes first
            sorry
    simp [h1]

  -- "By symmetry" part
  have h2 : MisereOutcomeL (g + g°) = PlayerOutcome.R := by
    unfold MisereOutcomeL
    have h2 : ¬(MisereOutcomeL_isL (g + g°)) := by
      unfold MisereOutcomeL_isL
      simp
      refine And.intro (fun _ => nonEmpty_Adjoint_left g) ?_
      intro k h3
      sorry
    simp [h2]
  simp [h1, h2]

theorem ne_zero_leftEnd_or_rightEnd {g : IGame} (h1 : g ≠ 0) : g.leftMoves ≠ ∅ ∨ g.rightMoves ≠ ∅ := by
  by_contra h2
  simp only [ne_eq, not_or, not_not] at h2
  obtain ⟨h2, h3⟩ := h2
  exact h1 (leftEmtpy_rightEmtpy_zero h2 h3)

theorem not_MisereEq_of_not_MisereGe {g h : IGame} (h1 : ¬MisereGe g h) : ¬MisereEq g h := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, h1⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  exact Ne.symm (ne_of_not_le h1)

/-- `o(G) ≥ P` is equivalent to "Left can win playing second on `G`" -/
theorem ge_P_Left_wins_second {g : IGame} (h1 : ¬MisereOutcomeR_isR g) : MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome
  unfold PlayerOutcomesToGameOutcome
  unfold MisereOutcomeR
  cases h2 : MisereOutcomeL g
  all_goals simp [h1, h2, Outcome.L_ge]

theorem left_in_P_in_LL {g gl : IGame} (h1 : gl ∈ g.leftMoves) (h2 : MisereOutcome gl = Outcome.P)
    : MisereOutcomeL_isL g := by
  unfold MisereOutcome at h2
  unfold PlayerOutcomesToGameOutcome at h2
  unfold MisereOutcomeL at h2
  unfold MisereOutcomeR at h2
  by_cases h3 : MisereOutcomeL_isL gl <;> by_cases h4 : MisereOutcomeR_isR gl <;> simp [h3, h4] at h2
  unfold MisereOutcomeL_isL
  refine Or.inr ?_
  use gl

theorem sum_of_left_ends_is_left_end {g h : IGame} (h1 : g.leftMoves = ∅) (h2 : h.leftMoves = ∅)
    : (g + h).leftMoves = ∅ := by
  simp [h1, h2]

theorem sum_of_left_ends_in_LL {g h : IGame} (h1 : g.leftMoves = ∅) (h2 : h.leftMoves = ∅)
    : MisereOutcomeL_isL (g + h) := MisereOutcomeL_isL_of_leftEnd (sum_of_left_ends_is_left_end h1 h2)

theorem theorem6_6 {g h : IGame} (h1 : h.leftMoves = ∅) (h2 : g.leftMoves ≠ ∅) : ¬MisereGe g h := by
  let t := {Set.range fun hr : h.rightMoves => Adjoint hr | { {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ } }ᴵ
  -- First consider H + T
  have h3 : MisereOutcome (h + t) ≥ Outcome.P := by
    apply ge_P_Left_wins_second
    unfold MisereOutcomeR_isR
    simp
    refine And.intro
      (fun _ => by simp only [IGame.rightMoves_ofSets, Set.singleton_ne_empty, not_false_eq_true, t])
      ?_
    intro x h3
    apply Or.elim h3 <;> clear h3 <;> intro ⟨hr, h3, h4⟩ <;> rw [<-h4]
    · -- If Right moves to H^R + T, then Left has a winning response to H^R + (H^R)°
      refine left_in_P_in_LL ?_ (proposition6_4 hr)
      refine IGame.add_left_mem_leftMoves_add ?_ hr
      simp only [IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop, t]
      exists hr
    · -- If instead Right moves to H + { | (G^L)°}, then Left wins outright,
      -- since (by the assumption on H) both components are Left ends
      refine sum_of_left_ends_in_LL h1 ?_
      simp only [IGame.rightMoves_ofSets, Set.mem_singleton_iff, t] at h3
      simp only [IGame.leftMoves_ofSets, h3, t]
  have h4 : MisereOutcome (g + t) ≤ Outcome.N := by
    sorry
  unfold MisereGe
  intro h5
  have h6 : MisereOutcome (g + t) ≥ Outcome.P :=
    Preorder.le_trans Outcome.P (MisereOutcome (h + t)) (MisereOutcome (g + t)) h3 (h5 t)
  cases h7 : MisereOutcome (g + t)
  all_goals simp [h7, instLEOutcome, Outcome.le', Outcome.lt'] at h4 h6

theorem corollary6_7 {g : IGame} (h1 : g ≠ 0) : ¬MisereEq g 0 := by
  apply Or.elim (ne_zero_leftEnd_or_rightEnd h1) <;> intro h2
  · exact not_MisereEq_of_not_MisereGe (theorem6_6 IGame.leftMoves_zero h2)
  · -- TODO: Right end variant of theorem6_6 and by symmetry
    sorry
