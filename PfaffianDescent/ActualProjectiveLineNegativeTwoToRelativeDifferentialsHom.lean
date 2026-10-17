import PfaffianDescent.ActualProjectiveLineNegativeTwoFrameTransition
import PfaffianDescent.SchemeModuleActualLocalHomGluing
import PfaffianDescent.SchemeModuleInternalHomRankOneTargetChart

/- SOURCE ONLY / UNVERIFIED. Construct a GLOBAL actual O(-2)→OmegaP1 map by
proving WHOLE local-Hom compatibility internally. Global invertibility is later. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist SchemeModuleInternalHom
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))
local notation "Xline" => projectiveLineProj K
local notation "Omega" => schemeRelativeDifferentials (projectiveLineProjToBase K)
local notation "NegTwo" => sheafOfModules (grading Iline) 2
private instance originalP1OmegaSectionModule (U : (Xline).Opens) :
    Module Γ(Xline, U) ((Omega).val.obj (op U)) := ((Omega).val.obj (op U)).isModule

/-- Original P1 coordinate opens, indexed by the original Bool variables. -/
def actualProjectiveLineCoordinateOpen (b : Bool) : (Xline).Opens :=
  Proj.basicOpen (grading Iline) (coordinate Iline b)

/-- Original actual normalized coordinate section on each original P1 open. -/
def actualProjectiveLineCoordinateSection (b : Bool) :
    Γ(Xline, actualProjectiveLineCoordinateOpen K b) :=
  (Proj.awayToSection (grading Iline) (coordinate Iline b))
    (chartCoordinate Iline b (!b))

/-- Original t/s chart section restricts to EXACT previously constructed overlap t/s. -/
theorem actualProjectiveLineCoordinateSection_false_overlap :
    (Xline).presheaf.map
      (homOfLE (Proj.basicOpen_mono (grading Iline) (coordinate Iline false)
        (coordinate Iline false * coordinate Iline true) ⟨coordinate Iline true, rfl⟩)).op
      (actualProjectiveLineCoordinateSection K false) = actualProjectiveLineOverlapT K := by
  have h := Proj.awayMap_awayToSection (grading Iline) (coordinate_mem Iline true)
    (rfl : coordinate Iline false * coordinate Iline true =
      coordinate Iline false * coordinate Iline true)
  exact (ConcreteCategory.congr_hom h (chartCoordinate Iline false true)).symm

/-- Original s/t chart section restricts to EXACT previously constructed overlap s/t. -/
theorem actualProjectiveLineCoordinateSection_true_overlap :
    (Xline).presheaf.map
      (homOfLE (Proj.basicOpen_mono (grading Iline) (coordinate Iline true)
        (coordinate Iline false * coordinate Iline true)
        ⟨coordinate Iline false, mul_comm _ _⟩)).op
      (actualProjectiveLineCoordinateSection K true) = actualProjectiveLineOverlapTInverse K := by
  have h := Proj.awayMap_awayToSection (grading Iline) (coordinate_mem Iline false)
    (mul_comm (coordinate Iline false) (coordinate Iline true))
  exact (ConcreteCategory.congr_hom h (chartCoordinate Iline true false)).symm

private theorem originalP1Restriction_comp
    {U V W : (Xline).Opens} (hVU : V ≤ U) (hWV : W ≤ V) (r : Γ(Xline, U)) :
    (Xline).presheaf.map (homOfLE hWV).op
      ((Xline).presheaf.map (homOfLE hVU).op r) =
        (Xline).presheaf.map (homOfLE (hWV.trans hVU)).op r :=
  (ConcreteCategory.congr_hom
    ((Xline).presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op) r).symm

/-- WHOLE native original chart differential transition on EVERY legitimate
subopen of their intersection, with the ORIGINAL restricted s/t coefficient. -/
theorem actualProjectiveLineCoordinateDifferentials_transition_subopen
    (V : (Xline).Opens)
    (hV0 : V ≤ actualProjectiveLineCoordinateOpen K false)
    (hV1 : V ≤ actualProjectiveLineCoordinateOpen K true) :
    (Omega).val.map (homOfLE hV1).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (actualProjectiveLineCoordinateOpen K true) (actualProjectiveLineCoordinateSection K true)) =
      -((Xline).presheaf.map (homOfLE hV1).op (actualProjectiveLineCoordinateSection K true) ^ 2) •
        (Omega).val.map (homOfLE hV0).op
          (actualRelativeDifferentialSection (projectiveLineProjToBase K)
            (actualProjectiveLineCoordinateOpen K false)
            (actualProjectiveLineCoordinateSection K false)) := by
  have hVC : V ≤ actualProjectiveLineCoordinateOverlap K := by
    change V ≤ Proj.basicOpen (grading Iline) (coordinate Iline false * coordinate Iline true)
    rw [Proj.basicOpen_mul]
    exact le_inf hV0 hV1
  let hC0 := Proj.basicOpen_mono (grading Iline) (coordinate Iline false)
    (coordinate Iline false * coordinate Iline true) ⟨coordinate Iline true, rfl⟩
  let hC1 := Proj.basicOpen_mono (grading Iline) (coordinate Iline true)
    (coordinate Iline false * coordinate Iline true) ⟨coordinate Iline false, mul_comm _ _⟩
  have h0 : (Xline).presheaf.map (homOfLE hV0).op (actualProjectiveLineCoordinateSection K false) =
      (Xline).presheaf.map (homOfLE hVC).op (actualProjectiveLineOverlapT K) := by
    rw [← actualProjectiveLineCoordinateSection_false_overlap K]
    exact (originalP1Restriction_comp K hC0 hVC _).symm
  have h1 : (Xline).presheaf.map (homOfLE hV1).op (actualProjectiveLineCoordinateSection K true) =
      (Xline).presheaf.map (homOfLE hVC).op (actualProjectiveLineOverlapTInverse K) := by
    rw [← actualProjectiveLineCoordinateSection_true_overlap K]
    exact (originalP1Restriction_comp K hC1 hVC _).symm
  have hprod : (Xline).presheaf.map (homOfLE hV0).op (actualProjectiveLineCoordinateSection K false) *
      (Xline).presheaf.map (homOfLE hV1).op (actualProjectiveLineCoordinateSection K true) = 1 := by
    rw [h0, h1, ← map_mul, actualProjectiveLineOverlapCoordinates_reciprocal, map_one]
  rw [actualRelativeDifferentialSection_restrict, actualRelativeDifferentialSection_restrict]
  exact actualRelativeDifferentialSection_inverseCoordinates (projectiveLineProjToBase K) V _ _ hprod

/-- The sign is - on the s/t chart, as dictated by genuine D(s/t) transition. -/
def actualProjectiveLineSignedCoordinateDifferential (b : Bool) :
    (Omega).val.obj (op (actualProjectiveLineCoordinateOpen K b)) :=
  if b = true then
    -actualRelativeDifferentialSection (projectiveLineProjToBase K)
      (actualProjectiveLineCoordinateOpen K b) (actualProjectiveLineCoordinateSection K b)
  else actualRelativeDifferentialSection (projectiveLineProjToBase K)
    (actualProjectiveLineCoordinateOpen K b) (actualProjectiveLineCoordinateSection K b)

/-- Actual native local O(-2)→Omega morphism, defined by original power frame
and genuine universal differential section, not a supplied local Iso. -/
def actualProjectiveLineNegativeTwoDifferentialLocalHom (b : Bool) :
    (NegTwo).over (actualProjectiveLineCoordinateOpen K b) ⟶
      (Omega).over (actualProjectiveLineCoordinateOpen K b) :=
  (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline b, coordinate_mem Iline b⟩).over (actualProjectiveLineCoordinateOpen K b) ≫
    unitSectionOver Omega (actualProjectiveLineCoordinateOpen K b)
      (actualProjectiveLineSignedCoordinateDifferential K b)

/-- WHOLE component values of the actual local map, including every smaller open. -/
theorem actualProjectiveLineNegativeTwoDifferentialLocalHom_apply
    (b : Bool) (V : Over (actualProjectiveLineCoordinateOpen K b))
    (z : (NegTwo).val.obj (op V.left)) :
    (actualProjectiveLineNegativeTwoDifferentialLocalHom K b).val.app (op V) z =
      (show Γ(Xline, V.left) from
        (nativeNegativeTwoPowerFrameHom (grading Iline)
          ⟨coordinate Iline b, coordinate_mem Iline b⟩).val.app (op V.left) z) •
        (show (Omega).val.obj (op V.left) from
          (Omega).val.map V.hom.op (actualProjectiveLineSignedCoordinateDifferential K b)) := rfl

/-- Carry the negative through the additive restriction map and prove the
square-coefficient identity BEFORE inserting any original sheaf factories. -/
private theorem originalSignedSquareCoefficientCompatibility007
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P]
    (a b c : R) (x : M) (l : P →+ M) (y : P)
    (ha : a = c ^ 2 * b) (hd : l y = -(c ^ 2) • x) :
    a • x = b • l (-y) := by
  rw [map_neg, ha, hd]
  simp only [neg_smul, neg_neg, smul_smul]
  exact congrArg (fun r : R => r • x) (mul_comm (c ^ 2) b)

/-- Actual original component compatibility, with all subset bounds legitimate
and all scalars carried by the SAME original smaller open. -/
theorem actualProjectiveLineNegativeTwoDifferentialLocal_component_compat
    (V : (Xline).Opens)
    (hV0 : V ≤ actualProjectiveLineCoordinateOpen K false)
    (hV1 : V ≤ actualProjectiveLineCoordinateOpen K true)
    (z : (NegTwo).val.obj (op V)) :
    (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline false, coordinate_mem Iline false⟩).val.app (op V) z •
      (Omega).val.map (homOfLE hV0).op (actualProjectiveLineSignedCoordinateDifferential K false) =
    (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline true, coordinate_mem Iline true⟩).val.app (op V) z •
      (Omega).val.map (homOfLE hV1).op (actualProjectiveLineSignedCoordinateDifferential K true) := by
  have hn := nativeNegativeTwoPowerFrameHom_transition (grading Iline)
    (⟨coordinate Iline true, coordinate_mem Iline true⟩ : grading Iline 1)
    (⟨coordinate Iline false, coordinate_mem Iline false⟩ : grading Iline 1) V hV1 z
  have hd := actualProjectiveLineCoordinateDifferentials_transition_subopen K V hV0 hV1
  change (show Γ(Xline, V) from
    (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline false, coordinate_mem Iline false⟩).val.app (op V) z) =
      @Mul.mul (Γ(Xline, V)) (inferInstance : Mul (Γ(Xline, V)))
        ((Xline).presheaf.map (homOfLE hV1).op (actualProjectiveLineCoordinateSection K true) ^ 2)
        (show Γ(Xline, V) from (nativeNegativeTwoPowerFrameHom (grading Iline)
          ⟨coordinate Iline true, coordinate_mem Iline true⟩).val.app (op V) z) at hn
  simp only [actualProjectiveLineSignedCoordinateDifferential, Bool.false_eq_true,
    not_false_eq_true, if_false, if_true] at ⊢
  exact originalSignedSquareCoefficientCompatibility007
    (show Γ(Xline, V) from (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline false, coordinate_mem Iline false⟩).val.app (op V) z)
    (show Γ(Xline, V) from (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline true, coordinate_mem Iline true⟩).val.app (op V) z)
    ((Xline).presheaf.map (homOfLE hV1).op (actualProjectiveLineCoordinateSection K true))
    ((Omega).val.map (homOfLE hV0).op
      (actualRelativeDifferentialSection (projectiveLineProjToBase K)
        (actualProjectiveLineCoordinateOpen K false) (actualProjectiveLineCoordinateSection K false)))
    ((Omega).val.map (homOfLE hV1).op).hom.toAddMonoidHom
    (actualRelativeDifferentialSection (projectiveLineProjToBase K)
      (actualProjectiveLineCoordinateOpen K true) (actualProjectiveLineCoordinateSection K true)) hn hd

/-- Proved WHOLE native internal-Hom section compatibility on each original overlap. -/
theorem actualProjectiveLineNegativeTwoDifferentialLocalHom_compatible (i j : Bool) :
    (SchemeModuleInternalHom.sheaf NegTwo Omega).val.map
      (homOfLE (show actualProjectiveLineCoordinateOpen K i ⊓ actualProjectiveLineCoordinateOpen K j ≤
        actualProjectiveLineCoordinateOpen K i from inf_le_left)).op
      ((sectionsEquivOver NegTwo Omega (actualProjectiveLineCoordinateOpen K i)).symm
        (actualProjectiveLineNegativeTwoDifferentialLocalHom K i)) =
    (SchemeModuleInternalHom.sheaf NegTwo Omega).val.map
      (homOfLE (show actualProjectiveLineCoordinateOpen K i ⊓ actualProjectiveLineCoordinateOpen K j ≤
        actualProjectiveLineCoordinateOpen K j from inf_le_right)).op
      ((sectionsEquivOver NegTwo Omega (actualProjectiveLineCoordinateOpen K j)).symm
        (actualProjectiveLineNegativeTwoDifferentialLocalHom K j)) := by
  cases i <;> cases j
  · rfl
  · apply Subtype.ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext z
    change _ = _
    exact actualProjectiveLineNegativeTwoDifferentialLocal_component_compat K V.unop.left
      (V.unop.hom.le.trans inf_le_left) (V.unop.hom.le.trans inf_le_right) z
  · apply Subtype.ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext z
    change _ = _
    exact (actualProjectiveLineNegativeTwoDifferentialLocal_component_compat K V.unop.left
      (V.unop.hom.le.trans inf_le_right) (V.unop.hom.le.trans inf_le_left) z).symm
  · rfl

/-- Original coordinate opens REALLY cover original P1. Lift only the finite index universe. -/
theorem actualProjectiveLineCoordinateOpen_lifted_cover :
    (⨆ i : ULift.{u} Bool, actualProjectiveLineCoordinateOpen K i.down) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨b, y, hy⟩ := exists_coordinate_chart Iline x
  apply Opens.mem_iSup.mpr
  refine ⟨ULift.up b, ?_⟩
  have hxy : x ∈ (chartι Iline b).opensRange := ⟨y, hy⟩
  change x ∈ (Proj.awayι (grading Iline) (coordinate Iline b)
    (coordinate_mem Iline b) Nat.zero_lt_one).opensRange at hxy
  change x ∈ Proj.basicOpen (grading Iline) (coordinate Iline b)
  simpa only [Proj.opensRange_awayι] using hxy

/-- GLOBAL actual O(-2)→Omega on ORIGINAL P1, obtained by GENUINE Hom-sheaf
gluing with internally PROVED whole local compatibility. No final Iso premise. -/
def actualProjectiveLineNegativeTwoToRelativeDifferentialsHom : NegTwo ⟶ Omega :=
  schemeModuleHomGlueOfActualCompatibleOverMorphisms NegTwo Omega
    (fun i : ULift.{u} Bool => actualProjectiveLineCoordinateOpen K i.down)
    (actualProjectiveLineCoordinateOpen_lifted_cover K)
    (fun i => actualProjectiveLineNegativeTwoDifferentialLocalHom K i.down)
    (fun i j => actualProjectiveLineNegativeTwoDifferentialLocalHom_compatible K i.down j.down)

/-- The constructed GLOBAL map restricts to the SAME entire original native local maps. -/
theorem actualProjectiveLineNegativeTwoToRelativeDifferentialsHom_homSection (b : Bool) :
    homSection (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)
      (actualProjectiveLineCoordinateOpen K b) =
        (sectionsEquivOver NegTwo Omega (actualProjectiveLineCoordinateOpen K b)).symm
          (actualProjectiveLineNegativeTwoDifferentialLocalHom K b) :=
  schemeModuleHomGlueOfActualCompatibleOverMorphisms_homSection NegTwo Omega
    (fun i : ULift.{u} Bool => actualProjectiveLineCoordinateOpen K i.down)
    (actualProjectiveLineCoordinateOpen_lifted_cover K)
    (fun i => actualProjectiveLineNegativeTwoDifferentialLocalHom K i.down)
    (fun i j => actualProjectiveLineNegativeTwoDifferentialLocalHom_compatible K i.down j.down)
    (ULift.up b)

end PfaffianDescent
end
