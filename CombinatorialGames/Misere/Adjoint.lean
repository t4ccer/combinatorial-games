/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.Misere.Outcome

open Classical in
noncomputable def Adjoint (g : IGame) : IGame :=
  if g = (0 : IGame) then ⋆
  else if IsLeftEnd g then {Set.range fun gr : g.rightMoves => Adjoint gr|{0}}ᴵ
  else if IsRightEnd g then {{0}|Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
  else { Set.range fun gr : g.rightMoves => Adjoint gr
       | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ
termination_by g
decreasing_by igame_wf

notation g"°" => Adjoint g

@[simp]
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
  by_cases h1 : g = 0 <;> simp [h1, IsRightEnd]
  by_cases h2 : g.leftMoves = ∅ <;> by_cases h3 : g.rightMoves = ∅ <;> simp [h2, h3]
  exact h1 (leftEnd_rightEnd_eq_zero h2 h3)

theorem mem_leftMoves_mem_adjoint_rightMoves {g gl : IGame} (h1 : gl ∈ g.leftMoves) :
    gl° ∈ (g°).rightMoves := by
  rw [Adjoint, IsLeftEnd, IsRightEnd]
  have h2 : g ≠ 0 := mem_leftMoves_ne_zero h1
  by_cases h3 : g.leftMoves = ∅ <;> by_cases h4 : g.rightMoves = ∅ <;> simp [*]
  · simp [h3] at h1
  · simp [h3] at h1
  · use gl
  · use gl

theorem mem_rightMoves_mem_adjoint_leftMoves {g gr : IGame} (h1 : gr ∈ g.rightMoves) :
    gr° ∈ (g°).leftMoves := by
  rw [Adjoint, IsLeftEnd, IsRightEnd]
  have h2 : g ≠ 0 := mem_rightMoves_ne_zero h1
  by_cases h3 : g.leftMoves = ∅ <;> by_cases h4 : g.rightMoves = ∅ <;> simp [*]
  · simp [h4] at h1
  · use gr
  · simp [h4] at h1
  · use gr

theorem mem_rightMoves_adjoint_exists_leftMoves {g gr : IGame} (h1 : gr ∈ g°.rightMoves)
    (h2 : ¬(IsLeftEnd g)) : ∃ gl ∈ g.leftMoves, gr = gl° := by
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

theorem mem_leftMoves_adjoint_exists_rightMoves {g gl : IGame} (h1 : gl ∈ g°.leftMoves)
    (h2 : ¬(IsRightEnd g)) : ∃ gr ∈ g.rightMoves, gl = gr° := by
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

theorem mem_adjoint_rightMoves_leftEnd_eq_zero {g gr : IGame} (h1 : gr ∈ g°.rightMoves)
    (h2 : IsLeftEnd g) : gr = 0 := by
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

theorem mem_adjoint_leftMoves_rightEnd_eq_zero {g gl : IGame} (h1 : gl ∈ g°.leftMoves)
    (h2 : IsRightEnd g) : gl = 0 := by
  unfold Adjoint at h1
  unfold IsRightEnd at h2
  by_cases h3 : g.leftMoves = ∅
  · have h4 : g = 0 := leftEnd_rightEnd_eq_zero h3 h2
    simp only [h4, reduceIte, IGame.leftMoves_star, Set.mem_singleton_iff] at h1
    exact h1
  · have h4 : g ≠ 0 := by
      intro h6
      simp only [h6, IGame.leftMoves_zero, not_true_eq_false] at h3
    simp only [h2, h3, h4, reduceIte, IsLeftEnd, IsRightEnd,
               IGame.leftMoves_ofSets, Set.mem_singleton_iff] at h1
    exact h1

theorem outcome_add_adjoint_eq_P (g : IGame) : MisereOutcome (g + g°) = Outcome.P := by
  unfold MisereOutcome PlayerOutcomesToGameOutcome
  -- By symmetry, it suffices to show that Left can win G + G° playing second
  have h1 : RightOutcome (g + Adjoint g) = PlayerOutcome.L := by
    unfold RightOutcome
    have h1 : ¬(RightWinsGoingFirst (g + g°)) := by
      rw [RightWinsGoingFirst_def]
      simp only [IGame.rightMoves_add, Set.mem_union, Set.mem_image, not_or, not_exists, not_and,
                 not_not]
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
      simp only [IGame.leftMoves_add, Set.mem_union, Set.mem_image, not_or, not_exists, not_and,
                 not_not]
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

instance short_adjoint (g : IGame) [h1 : IGame.Short g] : IGame.Short (g°) := by
  unfold Adjoint
  by_cases h2 : g = 0 <;> simp only [h2, reduceIte, IGame.instShortStar]
  by_cases h3 : IsLeftEnd g <;> simp [h3, reduceIte]
  · refine IGame.Short.mk' ?_ ?_ ?_ ?_
    · simp only [IGame.leftMoves_ofSets]
      exact Set.finite_range (fun gr : g.rightMoves => Adjoint gr)
    · simp only [IGame.rightMoves_ofSets, Set.finite_singleton]
    · simp only [IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop,
                 forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro gr h4
      have h5 : IGame.Short gr := IGame.Short.of_mem_rightMoves h4
      exact short_adjoint gr
    · simp only [IGame.rightMoves_ofSets, Set.mem_singleton_iff, forall_eq, IGame.Short.zero]
  · by_cases h4 : IsRightEnd g <;> simp [h4, reduceIte]
    · refine IGame.Short.mk' ?_ ?_ ?_ ?_
      · simp only [IGame.leftMoves_ofSets, Set.finite_singleton]
      · simp only [IGame.rightMoves_ofSets]
        exact Set.finite_range (fun gl : g.leftMoves => Adjoint gl)
      · simp only [IGame.leftMoves_ofSets, Set.mem_singleton_iff, forall_eq, IGame.Short.zero]
      · simp
        intro gl h5
        have h6 : IGame.Short gl := IGame.Short.of_mem_leftMoves h5
        exact short_adjoint gl
    · refine IGame.Short.mk' ?_ ?_ ?_ ?_
      · simp only [IGame.leftMoves_ofSets]
        exact Set.finite_range (fun gr : g.rightMoves => Adjoint gr)
      · simp only [IGame.rightMoves_ofSets]
        exact Set.finite_range (fun gl : g.leftMoves => Adjoint gl)
      · simp only [IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop,
                   forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro gr h5
        have h6 : IGame.Short gr := IGame.Short.of_mem_rightMoves h5
        exact short_adjoint gr
      · simp only [IGame.rightMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop,
                   forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro gl h5
        have h6 : IGame.Short gl := IGame.Short.of_mem_leftMoves h5
        exact short_adjoint gl
termination_by g
decreasing_by all_goals igame_wf
