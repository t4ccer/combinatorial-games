/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.Misere.Adjoint

noncomputable def leftEnd_not_leftEnd_not_ge.auxT (g h : IGame) : IGame :=
  { Set.range fun hr : h.rightMoves => Adjoint hr
  | { {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ } }ᴵ

instance {g h : IGame} [h1 : IGame.Short g] [h2 : IGame.Short h]
    : IGame.Short (leftEnd_not_leftEnd_not_ge.auxT g h) := by
  unfold leftEnd_not_leftEnd_not_ge.auxT
  refine IGame.Short.mk' ?_ ?_ ?_ ?_
  · simp only [IGame.leftMoves_ofSets]
    exact Set.finite_range (fun hr : h.rightMoves => Adjoint hr)
  · simp only [IGame.rightMoves_ofSets, Set.finite_singleton]
  · simp only [IGame.leftMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop,
               forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro hr h3
    have h4 := IGame.IsOption.short (IGame.IsOption.of_mem_rightMoves h3)
    exact short_adjoint hr
  · intro gl h3
    simp only [IGame.rightMoves_ofSets, Set.mem_singleton_iff] at h3
    rw [h3]
    refine IGame.Short.mk' ?_ ?_ ?_ ?_
    · simp only [IGame.leftMoves_ofSets, Set.finite_empty]
    · simp only [IGame.rightMoves_ofSets]
      exact Set.finite_range (fun gl : g.leftMoves ↦ Adjoint gl)
    · simp only [IGame.leftMoves_ofSets, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
    · simp only [IGame.rightMoves_ofSets, Set.mem_range, Subtype.exists, exists_prop,
                 forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro gl h4
      have h5 : IGame.Short gl := IGame.Short.of_mem_leftMoves h4
      exact short_adjoint gl

theorem leftEnd_not_leftEnd_not_ge {A : IGame → Prop} {g h : IGame}
    (h0 : A (leftEnd_not_leftEnd_not_ge.auxT g h)) (h1 : IsLeftEnd h)
    (h2 : ¬(IsLeftEnd g)) : ¬(g ≥m A h) := by
  let t := { Set.range fun hr : h.rightMoves => Adjoint hr
           | { {∅ | Set.range fun gl : g.leftMoves => Adjoint gl}ᴵ } }ᴵ

  -- First consider H + T
  have h3 : MisereOutcome (h + t) ≥ Outcome.P := by
    apply not_rightWinsGoingFirst_ge_P
    unfold RightWinsGoingFirst
    simp only [IGame.rightMoves_add, Set.union_empty_iff, Set.image_eq_empty, Set.mem_union,
               Set.mem_image, not_or, not_and, not_not]
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
      simp only [h3, IGame.leftMoves_ofSets, IsLeftEnd]
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
    Preorder.le_trans Outcome.P (MisereOutcome (h + t)) (MisereOutcome (g + t)) h3 (h5 t h0)
  cases h7 : MisereOutcome (g + t)
  all_goals simp only [t, h7, LE.le, LT.lt, and_false, and_self, and_true, ge_iff_le,
                       ne_eq, not_false_eq_true, not_true_eq_false, or_false, or_self, or_true,
                       reduceCtorEq] at h4 h6

alias theorem6_6 := leftEnd_not_leftEnd_not_ge

theorem HasNeg.rightEnd_not_rightEnd_not_ge {A : IGame → Prop} [HasNeg A] {g h : IGame}
    (h0 : A (leftEnd_not_leftEnd_not_ge.auxT (-g) (-h))) (h1 : IsRightEnd h)
    (h2 : ¬(IsRightEnd g)) : ¬(h ≥m A g) := by
  unfold IsRightEnd at h1 h2
  have h3 : IsLeftEnd (-h) := leftEnd_neg_iff_rightEnd.mpr h1
  have h4 : ¬(IsLeftEnd (-g)) := leftEnd_neg_iff_rightEnd.not.mpr h2
  have h5 : ¬((-g) ≥m A (-h)) := leftEnd_not_leftEnd_not_ge h0 h3 h4
  exact neg_ge_neg_iff.not.mp h5

class EqZeroIdentical (A : IGame → Prop) extends (HasNeg A) where
  has_T_g_zero {g : IGame} (h1 : A g) : A (leftEnd_not_leftEnd_not_ge.auxT g 0)

instance : EqZeroIdentical AnyGame where
  has_T_g_zero _ := trivial

instance : EqZeroIdentical IGame.Short where
  has_T_g_zero _ := instShortAuxT

theorem EqZeroIdentical.ne_zero_not_eq_zero {A : IGame → Prop} [EqZeroIdentical A] {g : IGame}
    (h0 : A g) (h1 : g ≠ 0) : ¬(g =m A 0) := by
  apply Or.elim (ne_zero_not_leftEnd_or_not_rightEnd h1) <;> intro h2
  · have h3 := leftEnd_not_leftEnd_not_ge (has_T_g_zero h0) IGame.leftMoves_zero h2
    exact not_MisereEq_of_not_MisereGe h3
  · intro h3
    have h4 : A (-g) := EqZeroIdentical.toHasNeg.has_neg g h0
    have h5 : A (leftEnd_not_leftEnd_not_ge.auxT (-g) (-0)) := by
      rw [neg_zero]
      exact has_T_g_zero h4
    exact not_MisereEq_of_not_MisereGe
            (HasNeg.rightEnd_not_rightEnd_not_ge h5 IGame.rightMoves_zero h2)
            (MisereEq_symm h3)

theorem EqZeroIdentical.eq_zero_iff_identical_zero {A : IGame → Prop} [EqZeroIdentical A]
    {g : IGame} (h0 : A g) : (g =m A 0 ↔ g = 0) := by
  constructor <;> intro h2
  · by_contra h3
    exact ne_zero_not_eq_zero h0 h3 h2
  · rw [h2]
    intro _
    exact congrFun rfl

theorem Transfinite.eq_zero_iff_identical_zero {g : IGame} :
    (g =m AnyGame 0 ↔ g = 0) := EqZeroIdentical.eq_zero_iff_identical_zero trivial

theorem Short.eq_zero_iff_identical_zero {g : IGame} [h1 : IGame.Short g] :
    (g =m IGame.Short 0 ↔ g = 0) := EqZeroIdentical.eq_zero_iff_identical_zero h1
