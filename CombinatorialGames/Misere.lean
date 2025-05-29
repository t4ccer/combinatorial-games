import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Special
import Mathlib.Data.Set.Operations

inductive Outcome where
  | L
  | N
  | P
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

-- TODO
def MisereOutcome : IGame → Outcome := sorry

def MisereEq (g h : IGame) : Prop := ∀ (x : IGame), MisereOutcome (g + x) = MisereOutcome (h + x)

def MisereGe (g h : IGame) : Prop := ∀ (x : IGame), MisereOutcome (g + x) ≥ MisereOutcome (h + x)

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

theorem Adjont_zero_def : Adjoint 0 = {{⋆}|{⋆}}ᴵ := by
  unfold Adjoint
  simp only [↓reduceIte]
