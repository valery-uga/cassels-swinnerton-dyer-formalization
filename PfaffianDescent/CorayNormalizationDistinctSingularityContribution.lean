import PfaffianDescent.CorayGenericNormalizationQuotientNativeStalkDefect
import PfaffianDescent.CorayOriginalPointAffineNormalizationDefectBound
import PfaffianDescent.SchemeModuleFiniteClosedSupportOriginalBaseGerms
import Mathlib.Topology.JacobsonSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! SOURCE ONLY / UNVERIFIED. Distinct original singular points contribute
additively to the SAME actual normalization quotient. Native normalization
finiteness and stalk comparison are constructed by the imported producers.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite closed support in a Jacobson space consists of closed points.
This discharges the genuine closed-point requirement of actual germ gluing. -/
theorem finiteClosedSubset_jacobson_isClosed_singleton
    {Y : Type u} [TopologicalSpace Y] [JacobsonSpace Y]
    (C : Set Y) (hC : C.Finite) (hclosed : IsClosed C) (x : C) :
    IsClosed ({x.1} : Set Y) := by
  letI : Fintype C := hC.fintype
  letI : JacobsonSpace C := JacobsonSpace.of_isClosedEmbedding hclosed.isClosedEmbedding_subtypeVal
  have hsingleton : IsClosed ({x} : Set C) := isClosed_singleton
  simpa only [Set.image_singleton] using
    hclosed.isClosedEmbedding_subtypeVal.isClosedMap ({x} : Set C) hsingleton

/-- The ACTUAL quotient's own native stalk has finite length at an original
closed curve point. Finite native integral closure is derived from a real
finite-type affine neighborhood; no local finiteness certificate is supplied. -/
theorem genericNormalizationQuotient_originalClosedPoint_nativeFiniteLength
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) (hdim : ringKrullDim (X.presheaf.stalk P.1) ≤ 1) :
    IsFiniteLength (X.presheaf.stalk P.1)
      ((schemeModuleStalkModuleFunctor X P.1).obj (genericNormalizationQuotientSheaf X)) := by
  have hx : P.1 ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hPU⟩ := Opens.mem_iSup.mp hx
  let R := X.presheaf.stalk P.1
  let F := X.functionField
  let Q := genericNormalizationQuotientSheaf X
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne R :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  letI : Module.Finite R (integralClosure R F) :=
    genericNormalization_nativeStalk_integralClosure_finite X pi U.1 U.2 ⟨P.1, hPU⟩
  letI := schemeModuleStalkModule Q P.1
  have hlength := localNormalizationDefect_isFiniteLength_of_finiteNormalization R F
  let E := genericNormalizationQuotientSheaf_affineNativeStalkDefectEquiv
    X U.1 U.2 ⟨P.1, hPU⟩
  exact E.symm.isFiniteLength hlength

/-- A genuinely singular original point lies in the ACTUAL quotient support
and contributes its FULL original residue degree to its OWN K-linear stalk.
The source K action is the independently original pi-induced one. -/
theorem genericNormalizationQuotient_originalClosedPoint_nonregular_stalkContribution
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) (hdim : ringKrullDim (X.presheaf.stalk P.1) ≤ 1)
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk P.1)) :
    P.1 ∈ schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ∧
      pi.residueDegree P.1 ≤ Module.finrank K
        (SchemeModuleStalkOver pi (genericNormalizationQuotientSheaf X) P.1) := by
  have hx : P.1 ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hPU⟩ := Opens.mem_iSup.mp hx
  let R := X.presheaf.stalk P.1
  let F := X.functionField
  let Q := genericNormalizationQuotientSheaf X
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne R :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  letI : Module K (localNormalizationDefect R F) :=
    Module.compHom _ (schemeStalkBaseRingHom pi P.1)
  letI : Nontrivial (localNormalizationDefect R F) :=
    localNormalizationDefect_nontrivial_of_not_isRegularLocalRing R F hsing
  let E := genericNormalizationQuotientSheaf_affineNativeStalkDefectGroundEquiv
    X pi U.1 U.2 ⟨P.1, hPU⟩
  have hnontrivial : Nontrivial (SchemeModuleStalkOver pi Q P.1) :=
    E.toEquiv.nontrivial_congr.mpr inferInstance
  letI : Nontrivial (SchemeModuleStalkOver pi Q P.1) := hnontrivial
  letI : Nontrivial ((schemeModuleStalkModuleFunctor X P.1).obj Q) := hnontrivial
  have hlength := genericNormalizationQuotient_originalClosedPoint_nativeFiniteLength X pi P hdim
  have hweight := (schemeModuleOriginalBaseStalk_finite_and_finrank pi Q P hlength).2
  have hpositive : 0 < Module.length R ((schemeModuleStalkModuleFunctor X P.1).obj Q) :=
    Module.length_pos
  have hone : 1 ≤ (Module.length R ((schemeModuleStalkModuleFunctor X P.1).obj Q)).toNat :=
    ENat.toNat_pos (ne_of_gt hpositive) (Module.length_ne_top_iff.mpr hlength)
  refine ⟨hnontrivial, ?_⟩
  calc
    pi.residueDegree P.1 = 1 * pi.residueDegree P.1 := (one_mul _).symm
    _ ≤ (Module.length R ((schemeModuleStalkModuleFunctor X P.1).obj Q)).toNat *
        pi.residueDegree P.1 := Nat.mul_le_mul_right _ hone
    _ = Module.finrank K (SchemeModuleStalkOver pi Q P.1) := hweight.symm

private theorem sum_comp_injective_le_sum
    {α β : Type*} [Fintype α] [Fintype β]
    (i : α → β) (hi : Function.Injective i) (w : β → ℕ) :
    ∑ a : α, w (i a) ≤ ∑ b : β, w b := by
  classical
  calc
    ∑ a : α, w (i a) = ∑ b ∈ Finset.univ.image i, w b :=
      (Finset.sum_image (fun a _ b _ hab => hi hab)).symm
    _ ≤ ∑ b : β, w b := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Distinct singular points contribute additively by distinct summands of
an ACTUAL global-germ decomposition. No desired additive inequality,
comparison equivalence, local length, or finite normalization is an input.
The natural support hypotheses are discharged by the projective caller. -/
theorem genericNormalizationQuotient_distinct_nonregular_residueSum_le_globalDefect
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (hfinite : (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)).Finite)
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (hdim : ∀ P : closedPoints X, ringKrullDim (X.presheaf.stalk P.1) ≤ 1)
    (D : Finset (closedPoints X))
    (hsing : ∀ P ∈ D, ¬ IsRegularLocalRing (X.presheaf.stalk P.1)) :
    ∑ P ∈ D, pi.residueDegree P.1 ≤
      Module.finrank K (SchemeModuleOpenSectionsOver pi (genericNormalizationQuotientSheaf X) ⊤) := by
  classical
  let Q := genericNormalizationQuotientSheaf X
  let C := schemeModuleStalkSupport Q
  letI : Fintype C := hfinite.fintype
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace pi
  have hpointClosed (x : X) (hx : x ∈ C) : IsClosed ({x} : Set X) :=
    finiteClosedSubset_jacobson_isClosed_singleton C hfinite hclosed ⟨x, hx⟩
  have hlength (x : C) : IsFiniteLength (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj Q) :=
    genericNormalizationQuotient_originalClosedPoint_nativeFiniteLength
      X pi ⟨x.1, hpointClosed x.1 x.2⟩ (hdim ⟨x.1, hpointClosed x.1 x.2⟩)
  have hglobal := schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    pi Q C hfinite hpointClosed Set.Subset.rfl hlength
  let w (x : C) := (Module.length (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj Q)).toNat * pi.residueDegree x.1
  let i (a : ↥D) : C :=
    ⟨a.1.1, (genericNormalizationQuotient_originalClosedPoint_nonregular_stalkContribution
      X pi a.1 (hdim a.1) (hsing a.1 a.2)).1⟩
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C => z.1) hab
  have hlocal (a : ↥D) : pi.residueDegree a.1.1 ≤ w (i a) := by
    have hb := (genericNormalizationQuotient_originalClosedPoint_nonregular_stalkContribution
      X pi a.1 (hdim a.1) (hsing a.1 a.2)).2
    have hw := (schemeModuleOriginalBaseStalk_finite_and_finrank
      pi Q a.1 (hlength (i a))).2
    exact hb.trans hw.le
  calc
    ∑ P ∈ D, pi.residueDegree P.1 = ∑ a : ↥D, pi.residueDegree a.1.1 :=
      (Finset.sum_coe_sort D (fun P => pi.residueDegree P.1)).symm
    _ ≤ ∑ a : ↥D, w (i a) := Finset.sum_le_sum (fun a _ => hlocal a)
    _ ≤ ∑ x : C, w x := sum_comp_injective_le_sum i hi w
    _ = Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) := hglobal.2.symm

end PfaffianDescent.Coray
