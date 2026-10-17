import PfaffianDescent.ClosedImmersionPushforwardExact
import PfaffianDescent.IdealSheafModule

/-!
# The two cohomology vanishings needed by Voisin's degree-ten argument

The Cassels application uses Voisin's Serre construction only with `l = 2`.
Consequently the surface cohomology input consists of

* `H¹(S, O_S(-3)) = 0`, for local freeness of the Serre extension; and
* `H¹(S, O_S) = 0`, for lifting quotient sections.

For a cubic hypersurface `i : S ⟶ P³`, the standard restriction sequences
reduce these to the four intermediate-cohomology vanishings

* `H¹(P³, O(-3)) = 0` and `H²(P³, O(-6)) = 0`; and
* `H¹(P³, O) = 0` and `H²(P³, O(-3)) = 0`.

This file performs that reduction in the Ext-based scheme-module cohomology
model used by the Serre construction.  The concrete construction of the
projective twists and the four ambient vanishings is kept as the remaining
projective-space calculation.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- A hypersurface restriction sequence on an ambient scheme gives the
degree-one cohomology vanishing of its coefficient module on the closed
subscheme.  The ambient inputs are exactly `H¹(B) = 0` and `H²(A) = 0` for
the sequence `0 ⟶ A ⟶ B ⟶ i_* M ⟶ 0`.

This combines the long exact cohomology sequence with the already proved
exact closed-immersion pushforward comparison. -/
theorem
    schemeModuleCohomology_one_subsingleton_of_closedImmersion_restrictionSequence
    {S P : Scheme.{u}} (i : S ⟶ P) [IsClosedImmersion i]
    [HasExt.{u} P.Modules] [HasExt.{u} S.Modules]
    [EnoughInjectives S.Modules]
    (M : S.Modules) (R : ShortComplex P.Modules) (hR : R.ShortExact)
    {A B : P.Modules} (eA : A ≅ R.X₁) (eB : B ≅ R.X₂)
    (eC : R.X₃ ≅ (Scheme.Modules.pushforward i).obj M)
    [Subsingleton (schemeModuleCohomology P B 1)]
    [Subsingleton (schemeModuleCohomology P A 2)] :
    Subsingleton (schemeModuleCohomology S M 1) := by
  let _ : Subsingleton (schemeModuleCohomology P
      ((Scheme.Modules.pushforward i).obj M) 1) :=
    schemeModuleCohomology_subsingleton_of_restriction_sequence_isos
      P R hR 1 eA eB eC
  exact
    schemeModuleCohomology_one_subsingleton_of_closedImmersion_pushforward
      i M

/-- The `l = 2` negative-twist vanishing in Voisin's Serre construction.

For the cubic restriction sequence
`0 ⟶ O_{P³}(-6) ⟶ O_{P³}(-3) ⟶ i_* O_S(-3) ⟶ 0`, it is enough to prove
the two displayed ambient vanishings.  The names of the ambient modules are
kept structural so the statement can be instantiated by the concrete
projective twisting sheaves once constructed. -/
theorem voisin_l2_negativeThree_cohomology_of_ambientRestriction
    {S P : Scheme.{u}} (i : S ⟶ P) [IsClosedImmersion i]
    [HasExt.{u} P.Modules] [HasExt.{u} S.Modules]
    [EnoughInjectives S.Modules]
    (OSminusThree : S.Modules)
    (OPminusSix OPminusThree : P.Modules)
    (R : ShortComplex P.Modules) (hR : R.ShortExact)
    (eMinusSix : OPminusSix ≅ R.X₁)
    (eMinusThree : OPminusThree ≅ R.X₂)
    (eRestriction : R.X₃ ≅
      (Scheme.Modules.pushforward i).obj OSminusThree)
    [Subsingleton (schemeModuleCohomology P OPminusThree 1)]
    [Subsingleton (schemeModuleCohomology P OPminusSix 2)] :
    Subsingleton (schemeModuleCohomology S OSminusThree 1) := by
  exact
    schemeModuleCohomology_one_subsingleton_of_closedImmersion_restrictionSequence
      i OSminusThree R hR eMinusSix eMinusThree eRestriction

/-- The structure-sheaf vanishing used to count sections in Voisin's
degree-ten Serre pencil.

For the cubic restriction sequence
`0 ⟶ O_{P³}(-3) ⟶ O_{P³} ⟶ i_* O_S ⟶ 0`, it follows from
`H¹(P³,O) = 0` and `H²(P³,O(-3)) = 0`. -/
theorem voisin_l2_structure_cohomology_of_ambientRestriction
    {S P : Scheme.{u}} (i : S ⟶ P) [IsClosedImmersion i]
    [HasExt.{u} P.Modules] [HasExt.{u} S.Modules]
    [EnoughInjectives S.Modules]
    (OPminusThree OP : P.Modules)
    (R : ShortComplex P.Modules) (hR : R.ShortExact)
    (eMinusThree : OPminusThree ≅ R.X₁)
    (eStructure : OP ≅ R.X₂)
    (eRestriction : R.X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit S.ringCatSheaf))
    [Subsingleton (schemeModuleCohomology P OP 1)]
    [Subsingleton (schemeModuleCohomology P OPminusThree 2)] :
    Subsingleton (schemeModuleCohomology S
      (SheafOfModules.unit S.ringCatSheaf) 1) := by
  exact
    schemeModuleCohomology_one_subsingleton_of_closedImmersion_restrictionSequence
      i (SheafOfModules.unit S.ringCatSheaf) R hR
        eMinusThree eStructure eRestriction

/-- The structure-sheaf half of the `l = 2` input using the canonical ideal
sequence of the actual closed immersion.  For a cubic hypersurface the ideal
module in the second ambient premise is `O_{P³}(-3)`, but no identification
with a separately constructed twist is needed to form the sequence or prove
the reduction. -/
theorem voisin_l2_structure_cohomology_of_closedImmersionIdeal
    {S P : Scheme.{u}} (i : S ⟶ P) [IsClosedImmersion i]
    [HasExt.{u} P.Modules] [HasExt.{u} S.Modules]
    [EnoughInjectives S.Modules]
    [Subsingleton (schemeModuleCohomology P
      (SheafOfModules.unit P.ringCatSheaf) 1)]
    [Subsingleton (schemeModuleCohomology P
      (IdealSheafDataModule.closedImmersionModule i) 2)] :
    Subsingleton (schemeModuleCohomology S
      (SheafOfModules.unit S.ringCatSheaf) 1) := by
  let R := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  exact
    schemeModuleCohomology_one_subsingleton_of_closedImmersion_restrictionSequence
      (A := IdealSheafDataModule.closedImmersionModule i)
      (B := SheafOfModules.unit P.ringCatSheaf)
      i (SheafOfModules.unit S.ringCatSheaf) R
        (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i)
        (Iso.refl _) (Iso.refl _) (Iso.refl _)

end PfaffianDescent
