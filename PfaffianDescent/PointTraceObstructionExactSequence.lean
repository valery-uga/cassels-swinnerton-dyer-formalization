import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # The exact extension obstruction to a point trace

These results use the actual quotient arrow of a short exact sequence.
They do not identify a local residue coordinate with a global trace.
For a canonical point trace, the missing geometric input is a bound on
extensions of the ideal sheaf, rather than nonzero local point Ext.

For a degree `d` closed point, an independent sufficient global input is
`finrank K (Ext I_point O(-1) 1) < d`, together with the relevant linear
structures and linearity of the boundary.  The expected sharp dimension
is `d - 1`.  No such dimension estimate is proved here.  In particular,
the subsingleton sufficient condition is suited to rational points and
must not be imposed on arbitrary degree points.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w

variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    {T : Type*} [AddCommGroup T]
    (trace : Ext.{w} S.X₂ Y 2 ≃+ T)

/-- A point class has zero global trace precisely when it comes from an
extension of the ideal term. -/
theorem pointTrace_zero_iff_extension_lift (z : Ext.{w} S.X₃ Y 2) :
    trace ((Ext.mk₀ S.g).comp z (zero_add 2)) = 0 ↔
      ∃ x : Ext.{w} S.X₁ Y 1, hS.extClass.comp x (by omega) = z := by
  constructor
  · intro hz
    have hpull : (Ext.mk₀ S.g).comp z (zero_add 2) = 0 :=
      trace.injective (hz.trans (map_zero trace).symm)
    exact Ext.contravariant_sequence_exact₃ hS Y z hpull (by omega)
  · rintro ⟨x, rfl⟩
    simp only [ShortComplex.ShortExact.comp_extClass_assoc, map_zero]

/-- Vanishing of every point trace is exactly surjectivity of the Serre
extension boundary. This isolates the genuinely global missing assertion. -/
theorem pointTrace_all_zero_iff_extension_boundary_surjective :
    (∀ z : Ext.{w} S.X₃ Y 2,
      trace ((Ext.mk₀ S.g).comp z (zero_add 2)) = 0) ↔
    Function.Surjective
      (fun x : Ext.{w} S.X₁ Y 1 => hS.extClass.comp x (show 1 + 1 = 2 by omega)) := by
  constructor
  · intro h z
    exact (pointTrace_zero_iff_extension_lift hS Y trace z).mp (h z)
  · intro h z
    exact (pointTrace_zero_iff_extension_lift hS Y trace z).mpr (h z)

include hS in
/-- For example, vanishing of canonical ideal Ext-one forces every nonzero
point class to have nonzero trace. The vanishing input is not supplied here. -/
theorem pointTrace_ne_zero_of_ideal_extOne_subsingleton
    [Subsingleton (Ext.{w} S.X₁ Y 1)]
    (z : Ext.{w} S.X₃ Y 2) (hz : z ≠ 0) :
    trace ((Ext.mk₀ S.g).comp z (zero_add 2)) ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := (pointTrace_zero_iff_extension_lift hS Y trace z).mp hzero
  apply hz
  rw [← hx, Subsingleton.elim x 0, Ext.comp_zero]

end PfaffianDescent

