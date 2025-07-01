import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Special
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
  else if IsLeftEnd g then {Set.range fun gr : g.rightMoves => Adjoint gr|{0}}ᴵ
  else if IsRightEnd g then {{0}|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
  else {Set.range fun gr : g.rightMoves => Adjoint gr|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
termination_by g
decreasing_by igame_wf

notation g"°" => Adjoint g

theorem Adjont_zero_def : 0° = ⋆ := by
  unfold Adjoint
  simp only [reduceIte]

theorem leftEnd_rightEnd_zero {g : IGame} (hl : IsLeftEnd g) (hr : IsRightEnd g) : g = 0 := by
  rw [IGame.zero_def]
  rw [IsLeftEnd] at hl
  rw [IsRightEnd] at hr
  ext
  · simp only [hl, Set.mem_empty_iff_false, IGame.leftMoves_ofSets]
  · simp only [hr, Set.mem_empty_iff_false, IGame.rightMoves_ofSets]

theorem adjoint_not_leftEnd (g : IGame) : ¬(IsLeftEnd (g°)) := by
  unfold Adjoint
  unfold IsLeftEnd
  by_cases h1 : g = 0 <;> simp [h1, IsLeftEnd, IsRightEnd]
  by_cases h2 : g.leftMoves = ∅ <;> by_cases h3 : g.rightMoves = ∅ <;> simp [IsLeftEnd, h2, h3]
  exact h1 (leftEnd_rightEnd_zero h2 h3)

theorem adjoint_not_rightEnd (g : IGame) : ¬(IsRightEnd (g°)) := by
  unfold Adjoint IsRightEnd
  by_cases h1 : g = 0 <;> simp [h1]
  by_cases h2 : g.leftMoves = ∅ <;> simp [IsLeftEnd, h2]
  by_cases h3 : g.rightMoves = ∅ <;> simp [h3, h2]

theorem rightMoves_of_Adjoint_of_leftEnd {g : IGame} (h1 : IsLeftEnd g) : g°.rightMoves = {0} := by
  unfold IsLeftEnd at h1
  unfold Adjoint
  by_cases h2 : g = 0 <;> simp [IsLeftEnd, IsRightEnd, h1, h2]

theorem MisereOutcomeL_isL_of_leftEnd {g : IGame} (h1 : IsLeftEnd g) : LeftWinsGoingFirst g := by
  unfold LeftWinsGoingFirst
  exact Or.symm (Or.inr h1)

theorem MisereOutcomeR_isR_of_rightEnd {g : IGame} (h : IsRightEnd g) : RightWinsGoingFirst g := by
  unfold RightWinsGoingFirst
  exact Or.symm (Or.inr h)

theorem ne_zero_not_leftEnd_or_not_rightEnd {g : IGame} (h1 : g ≠ 0) : ¬(IsLeftEnd g) ∨ ¬(IsRightEnd g) := by
  by_contra h2
  simp only [ne_eq, not_or, not_not] at h2
  obtain ⟨h2, h3⟩ := h2
  exact h1 (leftEnd_rightEnd_zero h2 h3)

theorem not_MisereEq_of_not_MisereGe {g h : IGame} (h1 : ¬MisereGe g h) : ¬MisereEq g h := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, h1⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  exact Ne.symm (ne_of_not_le h1)

/-- `o(G) ≥ P` is equivalent to "Left can win playing second on `G`" -/
theorem ge_P_Left_wins_second {g : IGame} (h1 : ¬RightWinsGoingFirst g) : MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome RightOutcome
  cases h2 : LeftOutcome g
  all_goals simp [h1, h2, Outcome.L_ge]

theorem le_P_Right_wins_second {g : IGame} (h1 : ¬LeftWinsGoingFirst g) : MisereOutcome g ≤ Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome
  cases h2 : LeftOutcome g <;> cases h3 : RightOutcome g
  all_goals simp [h1, h2, h3, Outcome.ge_R]

theorem left_in_P_in_LL {g gl : IGame} (h1 : gl ∈ g.leftMoves) (h2 : MisereOutcome gl = Outcome.P)
    : LeftWinsGoingFirst g := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome RightOutcome at h2
  by_cases h3 : LeftWinsGoingFirst gl <;> by_cases h4 : RightWinsGoingFirst gl <;> simp [h3, h4] at h2
  rw [LeftWinsGoingFirst_def]
  exact Or.inr (by use gl)

theorem right_in_P_in_RR {g gr : IGame} (h1 : gr ∈ g.rightMoves) (h2 : MisereOutcome gr = Outcome.P)
    : RightWinsGoingFirst g := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome RightOutcome at h2
  by_cases h3 : RightWinsGoingFirst gr <;> by_cases h4 : LeftWinsGoingFirst gr <;> simp [h3, h4] at h2
  rw [RightWinsGoingFirst_def]
  exact Or.inr (by use gr)

theorem sum_of_left_ends_is_left_end {g h : IGame} (h1 : IsLeftEnd g) (h2 : IsLeftEnd h) : IsLeftEnd (g + h) := by
  unfold IsLeftEnd at h1 h2
  simp [h1, h2, IsLeftEnd]

theorem sum_of_right_ends_is_right_end {g h : IGame} (h1 : g.rightMoves = ∅) (h2 : h.rightMoves = ∅)
    : (g + h).rightMoves = ∅ := by
  simp [h1, h2]

theorem add_leftEnd_LeftWinsGoingFirst {g h : IGame} (h1 : IsLeftEnd g) (h2 : IsLeftEnd h)
    : LeftWinsGoingFirst (g + h) := MisereOutcomeL_isL_of_leftEnd (sum_of_left_ends_is_left_end h1 h2)

theorem add_rightEnd_RightWinsGoingFirst {g h : IGame} (h1 : IsRightEnd g) (h2 : IsRightEnd h)
    : RightWinsGoingFirst (g + h) := MisereOutcomeR_isR_of_rightEnd (sum_of_right_ends_is_right_end h1 h2)

theorem le_N_Right_wins_first {g : IGame} (h1 : RightWinsGoingFirst g) : MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome RightOutcome
  cases h2 : LeftOutcome g
  all_goals simp [h1, h2, Outcome.L_ge, Outcome.ge_R]

theorem ge_N_Left_wins_first {g : IGame} (h1 : LeftWinsGoingFirst g) : MisereOutcome g ≥ Outcome.N := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome
  cases h2 : RightOutcome g
  all_goals simp [h1, h2, Outcome.L_ge, Outcome.ge_R]

theorem P_ne_LL {g : IGame} (h1 : MisereOutcome g = Outcome.P) : ¬LeftWinsGoingFirst g := by
  intro h2
  unfold MisereOutcome PlayerOutcomesToGameOutcome LeftOutcome at h1
  cases h3 : RightOutcome g <;> simp only [h2, h3, reduceIte, reduceCtorEq] at h1

theorem P_ne_RR {g : IGame} (h1 : MisereOutcome g = Outcome.P) : ¬RightWinsGoingFirst g := by
  intro h2
  unfold MisereOutcome PlayerOutcomesToGameOutcome RightOutcome at h1
  cases h3 : LeftOutcome g <;> simp only [h2, h3, reduceIte, reduceCtorEq] at h1

theorem mem_left_ne_zero {g gl : IGame} (h1 : gl ∈ g.leftMoves) : g ≠ 0 := by
  intro h2
  simp [h2] at h1

theorem mem_right_ne_zero {g gr : IGame} (h1 : gr ∈ g.rightMoves) : g ≠ 0 := by
  intro h2
  simp [h2] at h1

theorem mem_left_mem_adjoint_right {g gl : IGame} (h1 : gl ∈ g.leftMoves) : gl° ∈ (g°).rightMoves := by
  rw [Adjoint, IsLeftEnd, IsRightEnd]
  have h2 : g ≠ 0 := mem_left_ne_zero h1
  by_cases h3 : g.leftMoves = ∅ <;> by_cases h4 : g.rightMoves = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

theorem mem_right_mem_adjoint_left {g gr : IGame} (h1 : gr ∈ g.rightMoves) : gr° ∈ (g°).leftMoves := by
  rw [Adjoint, IsLeftEnd, IsRightEnd]
  have h2 : g ≠ 0 := mem_right_ne_zero h1
  by_cases h3 : g.leftMoves = ∅ <;> by_cases h4 : g.rightMoves = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem mem_right_adjoint_exists_left {g gr : IGame}
  (h1 : gr ∈ g°.rightMoves) (h2 : ¬(IsLeftEnd g))
    : ∃ gl ∈ g.leftMoves, gr = gl° := by
  unfold Adjoint IsLeftEnd IsRightEnd at h1
  unfold IsLeftEnd at h2
  have h2 : g ≠ 0 := by
    intro h3
    simp [h3] at h2
  by_cases h3 : g.rightMoves = ∅
  all_goals
  · simp[*] at h1
    obtain ⟨x, h2, h3⟩ := h1
    use x
    apply And.intro h2
    exact Eq.symm h3

theorem proposition6_4 (g : IGame) : MisereOutcome (g + g°) = Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome
  -- By symmetry, it suffices to show that Left can win G + G° playing second
  have h1 : RightOutcome (g + Adjoint g) = PlayerOutcome.L := by
    unfold RightOutcome
    have h1 : ¬(RightWinsGoingFirst (g + g°)) := by
      rw [RightWinsGoingFirst_def]
      simp
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
        · have h5 : gr° ∈ g°.leftMoves := mem_right_mem_adjoint_left h2
          have h6 : gr + gr° ∈ (gr + g°).leftMoves :=
            IGame.add_left_mem_leftMoves_add (mem_right_mem_adjoint_left h2) gr
          rw [LeftWinsGoingFirst_def]
          apply Or.inr
          use gr + gr°
          exact And.intro h6 (P_ne_RR (proposition6_4 gr))
        · rw [LeftWinsGoingFirst_def]
          by_cases h3 : g.leftMoves = ∅
          · apply Or.inl
            have h4 : gr = 0 := by
              unfold Adjoint at h2
              by_cases h5 : g.rightMoves = ∅
              · have h6 : g = 0 := leftEnd_rightEnd_zero h3 h5
                simp[*] at *
                exact h2
              · have h6 : g ≠ 0 := by
                  intro h6
                  simp [h6] at h5
                simp [IsLeftEnd, IsRightEnd,  h3, h6] at h2
                exact h2
            simp [h4]
            exact h3
          · apply Or.inr
            have ⟨gl, h3, h4⟩ := mem_right_adjoint_exists_left h2 h3
            rw [h4]
            use gl + gl°
            constructor
            · exact IGame.add_right_mem_leftMoves_add h3 (gl°)
            · exact P_ne_RR (proposition6_4 gl)
    simp [h1]

  -- "By symmetry" part
  have h2 : LeftOutcome (g + g°) = PlayerOutcome.R := by
    unfold LeftOutcome
    have h2 : ¬(LeftWinsGoingFirst (g + g°)) := by
      rw [LeftWinsGoingFirst_def]
      sorry
    simp [h2]
  simp [h1, h2]
termination_by g
decreasing_by all_goals igame_wf

theorem theorem6_6 {g h : IGame} (h1 : IsLeftEnd h) (h2 : ¬(IsLeftEnd g)) : ¬MisereGe g h := by
  let t := {Set.range fun hr : h.rightMoves => Adjoint hr | { {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ } }ᴵ
  -- First consider H + T
  have h3 : MisereOutcome (h + t) ≥ Outcome.P := by
    apply ge_P_Left_wins_second
    unfold RightWinsGoingFirst
    simp only [IGame.rightMoves_add, Set.union_empty_iff, Set.image_eq_empty, Set.mem_union,
               Set.mem_image, not_or, not_and, not_exists, not_not]
    apply And.intro (fun _ => by
      simp only [IGame.rightMoves_ofSets, Set.singleton_ne_empty, not_false_eq_true, t])
    intro x h3
    apply Or.elim h3 <;> clear h3 <;> intro ⟨hr, h3, h4⟩ <;> rw [<-h4]
    · -- If Right moves to H^R + T, then Left has a winning response to H^R + (H^R)°
      refine left_in_P_in_LL ?_ (proposition6_4 hr)
      refine IGame.add_left_mem_leftMoves_add ?_ hr
      simp only [IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop, t]
      exists hr
    · -- If instead Right moves to H + { | (G^L)°}, then Left wins outright,
      -- since (by the assumption on H) both components are Left ends
      apply add_leftEnd_LeftWinsGoingFirst h1
      simp only [IGame.rightMoves_ofSets, Set.mem_singleton_iff, t] at h3
      simp only [IGame.leftMoves_ofSets, IsLeftEnd, h3, t]
  -- Next consider G + T
  have h4 : MisereOutcome (g + t) ≤ Outcome.N := by
    apply le_N_Right_wins_first
    rw [RightWinsGoingFirst_def]
    apply Or.inr
    -- Right has a move to G + { | (G^L)° }
    use (g + {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ)
    constructor
    · refine IGame.add_left_mem_rightMoves_add ?_ g
      simp only [IGame.rightMoves_ofSets, Set.mem_singleton_iff, t]
    · rw [LeftWinsGoingFirst_def]
      simp only [IGame.leftMoves_add, IGame.leftMoves_ofSets, Set.image_empty, Set.union_empty,
                 Set.image_eq_empty, Set.mem_image, exists_exists_and_eq_and, not_or, not_exists,
                 not_and, not_not, t, IsLeftEnd]
      apply And.intro h2
      intro gl h4
      -- from which Left's only options have the form G^L + { | (G^L)° }
      rw [RightWinsGoingFirst_def]
      apply Or.inr
      -- There must be at least one such option, by the assumption on G;
      -- and each such option has a mirror-image response by Right, to G^L + (G^L)°
      use (gl + gl°)
      refine And.intro ?_ (P_ne_LL (proposition6_4 gl))
      refine IGame.add_left_mem_rightMoves_add ?_ gl
      simp only [IGame.rightMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop, t]
      use gl
  unfold MisereGe
  intro h5
  have h6 : MisereOutcome (g + t) ≥ Outcome.P :=
    Preorder.le_trans Outcome.P (MisereOutcome (h + t)) (MisereOutcome (g + t)) h3 (h5 t)
  cases h7 : MisereOutcome (g + t)
  all_goals simp [h7, instLEOutcome, Outcome.le', Outcome.lt'] at h4 h6

-- Manual version of theorem6_6'' to not use sorry cause I can't prove `MisereEq_negAux` rn
theorem theorem6_6' {g h : IGame} (h1 : IsRightEnd h) (h2 : ¬(IsRightEnd g)) : ¬MisereGe h g := by
  let t := { { { Set.range fun gr : g.rightMoves => Adjoint gr | ∅ }ᴵ } | Set.range fun hl : h.leftMoves => Adjoint hl }ᴵ
  have h3 : MisereOutcome (h + t) ≤ Outcome.P := by
    apply le_P_Right_wins_second
    unfold LeftWinsGoingFirst
    simp only [IGame.leftMoves_add, Set.union_empty_iff, Set.image_eq_empty, Set.mem_union,
               Set.mem_image, not_or, not_and, not_exists, not_not]
    apply And.intro (fun _ => by
      simp only [IGame.leftMoves_ofSets, Set.singleton_ne_empty, not_false_eq_true, t])
    intro x h3
    apply Or.elim h3 <;> clear h3 <;> intro ⟨hl, h3, h4⟩ <;> rw [<-h4]
    · refine right_in_P_in_RR ?_ (proposition6_4 hl)
      refine IGame.add_left_mem_rightMoves_add ?_ hl
      simp only [IGame.rightMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop, t]
      exists hl
    · apply add_rightEnd_RightWinsGoingFirst h1
      simp only [t, IGame.leftMoves_ofSets, Set.mem_singleton_iff] at h3
      simp only [h3, IGame.rightMoves_ofSets, IsRightEnd]
  have h4 : MisereOutcome (g + t) ≥ Outcome.N := by
    apply ge_N_Left_wins_first
    rw [LeftWinsGoingFirst_def]
    apply Or.inr
    use (g + { Set.range fun gr : g.rightMoves => Adjoint gr | ∅ }ᴵ)
    constructor
    · refine IGame.add_left_mem_leftMoves_add ?_ g
      simp only [IGame.leftMoves_ofSets, Set.mem_singleton_iff, t]
    · rw [RightWinsGoingFirst_def]
      simp only [IGame.rightMoves_add, IGame.rightMoves_ofSets, Set.image_empty, Set.union_empty,
                 Set.image_eq_empty, Set.mem_image, exists_exists_and_eq_and, not_or, not_exists,
                 not_and, not_not, t, IsRightEnd]
      apply And.intro h2
      intro gr h4
      rw [LeftWinsGoingFirst_def]
      apply Or.inr
      use (gr + gr°)
      refine And.intro ?_ (P_ne_RR (proposition6_4 gr))
      refine IGame.add_left_mem_leftMoves_add ?_ gr
      simp only [IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop, t]
      use gr
  unfold MisereGe
  intro h5
  have h6 : MisereOutcome (g + t) ≤ Outcome.P :=
    Preorder.le_trans (MisereOutcome (g + t)) (MisereOutcome (h + t)) Outcome.P (h5 t) h3
  cases h7 : MisereOutcome (g + t)
  all_goals simp [h7, instLEOutcome, Outcome.le', Outcome.lt'] at h4 h6

theorem MisereEq_negAux {g h : IGame} (h1 : MisereGe g h): MisereGe (-h) (-g) := by
  sorry -- Alfie said so

theorem MisereEq_neg {g h : IGame} : (MisereGe g h ↔ MisereGe (-h) (-g)) := by
  constructor <;> intro h1
  · exact MisereEq_negAux h1
  · have h2 := MisereEq_negAux h1
    simp only [neg_neg] at h2
    exact h2

theorem theorem6_6'' {g h : IGame} (h1 : IsRightEnd h) (h2 : ¬(IsRightEnd g)) : ¬MisereGe h g := by
  unfold IsRightEnd at h1 h2
  have h3 : (-h).leftMoves = ∅ := by
    simp only [IGame.leftMoves_neg, h1, Set.neg_empty]
  have h4 : (-g).leftMoves ≠ ∅ := by
    simp only [IGame.leftMoves_neg, ne_eq, Set.neg_eq_empty, h2, not_false_eq_true]
  have h5 := theorem6_6 h3 h4
  intro h6
  exact h5 (MisereEq_neg.mp h6)

theorem MisereEq_symm {g h : IGame} (h1 : MisereEq g h) : MisereEq h g := by
  intro x
  exact Eq.symm (h1 x)

theorem corollary6_7 {g : IGame} (h1 : g ≠ 0) : ¬MisereEq g 0 := by
  apply Or.elim (ne_zero_not_leftEnd_or_not_rightEnd h1) <;> intro h2
  · exact not_MisereEq_of_not_MisereGe (theorem6_6 IGame.leftMoves_zero h2)
  · intro h3
    exact (not_MisereEq_of_not_MisereGe (theorem6_6' IGame.rightMoves_zero h2)) (MisereEq_symm h3)
