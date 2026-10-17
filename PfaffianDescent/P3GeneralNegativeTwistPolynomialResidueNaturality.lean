import PfaffianDescent.P3GeneralNegativeTwistTopResidueGroundLinear
import PfaffianDescent.P3QuadraticLaurentMultiplication
import PfaffianDescent.ExtSourceIsoCoefficientNaturality
import Mathlib.LinearAlgebra.Dual.Basis

/-! Arbitrary-degree ORIGINAL-K top residue pairing and genuine polynomial
multiplication naturality. This extends the existing degree-two calculation
to every nonempty full-negative residue degree. It supplies the necessary
cubic annihilator bridge for the original p/q H¹ bound, not that bound itself.
SOURCE ONLY / UNVERIFIED. No comparison/naturality certificate is assumed. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ordinary degree-d monomial exponents. -/
abbrev P3HomogeneousExponent (d : ℕ) := {b : Fin 4 →₀ ℕ // b.degree = d}

instance p3HomogeneousExponent_finite (d : ℕ) : Finite (P3HomogeneousExponent d) := by
  have hs : ({b : Fin 4 →₀ ℕ | b.degree = d} : Set (Fin 4 →₀ ℕ)).Finite :=
    (Finsupp.finite_of_degree_le d).subset (by intro b hb; exact hb.le)
  exact hs.to_subtype

noncomputable instance p3HomogeneousExponent_fintype (d : ℕ) :
    Fintype (P3HomogeneousExponent d) := Fintype.ofFinite _

/-- The genuine standard monomial basis, for arbitrary degree d. -/
def p3HomogeneousMonomialBasis (d : ℕ) : Module.Basis (P3HomogeneousExponent d) K (PS d) :=
  (MvPolynomial.basisRestrictSupport K {b : Fin 4 →₀ ℕ | b.degree = d}).map
    (LinearEquiv.ofEq (MvPolynomial.restrictSupport K {b : Fin 4 →₀ ℕ | b.degree = d})
      (PS d) (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 4) K d).symm)

theorem p3HomogeneousMonomialBasis_apply_coe (d : ℕ) (b : P3HomogeneousExponent d) :
    ((p3HomogeneousMonomialBasis K d b : PS d) : MvPolynomial (Fin 4) K) =
      MvPolynomial.monomial b.1 1 := by
  change (((MvPolynomial.basisRestrictSupport K
    {b : Fin 4 →₀ ℕ | b.degree = d}) b :
      MvPolynomial.restrictSupport K {b : Fin 4 →₀ ℕ | b.degree = d}) :
        MvPolynomial (Fin 4) K) = _
  change ((AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
    {b : Fin 4 →₀ ℕ | b.degree = d}).symm (Finsupp.single b 1) :
      MvPolynomial (Fin 4) K) = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp, MvPolynomial.single_eq_monomial]

def p3HomogeneousDualCoordinateEquiv (d : ℕ) :
    Module.Dual K (PS d) ≃ₗ[K] (P3HomogeneousExponent d → K) :=
  (p3HomogeneousMonomialBasis K d).dualBasis.equivFun

theorem p3HomogeneousDualCoordinateEquiv_apply (d : ℕ)
    (phi : Module.Dual K (PS d)) (b : P3HomogeneousExponent d) :
    p3HomogeneousDualCoordinateEquiv K d phi b = phi (p3HomogeneousMonomialBasis K d b) :=
  Module.Basis.dualBasis_equivFun (p3HomogeneousMonomialBasis K d) phi b

/-- Genuine polynomial multiplication followed by the canonical Laurent
coefficient; linear in the polynomial for its original K action. -/
def p3HomogeneousLaurentResidueLinearMap (d : ℕ) (w : LaurentLocalization.LaurentPolynomial K) :
    Module.Dual K (PS d) where
  toFun q := (polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) * w).coeff
    (p3SerreDualExponent 0)
  map_add' q q' := by
    change (polynomialToLaurent (K := K)
      ((q : MvPolynomial (Fin 4) K) + (q' : MvPolynomial (Fin 4) K)) * w).coeff _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' c q := by
    change (polynomialToLaurent (K := K) (c • (q : MvPolynomial (Fin 4) K)) * w).coeff _ = _
    have hs : polynomialToLaurent (K := K) (c • (q : MvPolynomial (Fin 4) K)) =
        c • polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) := by
      ext a
      change (Finsupp.mapDomain exponentToInt
        (c • AddMonoidAlgebra.coeff (q : MvPolynomial (Fin 4) K))) a =
        (c • Finsupp.mapDomain exponentToInt
          (AddMonoidAlgebra.coeff (q : MvPolynomial (Fin 4) K))) a
      rw [Finsupp.mapDomain_smul]
    rw [hs, smul_mul_assoc, AddMonoidAlgebra.coeff_smul_apply]
    rfl

theorem p3HomogeneousLaurentResidueLinearMap_monomial
    (d : ℕ) (w : LaurentLocalization.LaurentPolynomial K) (b : P3HomogeneousExponent d) :
    p3HomogeneousLaurentResidueLinearMap K d w (p3HomogeneousMonomialBasis K d b) =
      w.coeff (p3SerreDualExponent b.1) := by
  change (polynomialToLaurent (K := K)
    ((p3HomogeneousMonomialBasis K d b : PS d) : MvPolynomial (Fin 4) K) * w).coeff
      (p3SerreDualExponent 0) = _
  rw [p3HomogeneousMonomialBasis_apply_coe, polynomialToLaurent_monomial,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  simp [p3SerreDualExponent, sub_eq_add_neg]

/-- The SAME original-K residue injection, expressed as the ordinary
homogeneous-polynomial dual. hdegree only records the true index relation;
no cohomology pairing or naturality conclusion is a premise. -/
def p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap
    [HasExt.{u} (Proj PS).Modules] (m d : ℕ) (hdegree : d + 4 = m) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
    schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3 →ₗ[K]
      Module.Dual K (PS d) := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
  let E := p3HomogeneousDualCoordinateEquiv K d
  let R := p3NegativeTwistCohomologyThreeResidueLinearMap K m
  refine
    { toFun := fun z => E.symm (fun b => R z ⟨b.1, by rw [b.2, hdegree]⟩)
      map_add' := ?_
      map_smul' := ?_ }
  · intro z z'
    apply E.injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    funext b
    rfl
  · intro c z
    apply E.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    funext b
    rfl

/-- Every coordinate of the previous actual residue injection is retained. -/
theorem p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_injective
    [HasExt.{u} (Proj PS).Modules] (m d : ℕ) (hdegree : d + 4 = m) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
    Function.Injective (p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K m d hdegree) := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
  intro z z' hz
  apply p3NegativeTwistCohomologyThreeResidueLinearMap_injective K m
  funext b
  have hb : b.1.degree = d := by have h := b.2; omega
  have h := congrArg (p3HomogeneousDualCoordinateEquiv K d) hz
  have hc := congrFun h (⟨b.1, hb⟩ : P3HomogeneousExponent d)
  simpa only [p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply, Subtype.coe_eta] using hc

/-- On the actual raw representative, the new dual is literally the
multiply-then-extract Laurent pairing, for every polynomial degree. -/
theorem p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_raw
    [HasExt.{u} (Proj PS).Modules] (m d : ℕ) (hdegree : d + 4 = m)
    (w : P3RawTopCocycle K m) :
    p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K m d hdegree
        (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
          (p3RawTopCocycleToAugmentedExt K m w)) =
      p3HomogeneousLaurentResidueLinearMap K d
        (p3NegativeTwistCechTermToLaurent K m 3 w.1 id) := by
  apply (p3HomogeneousMonomialBasis K d).ext
  intro b
  rw [p3HomogeneousLaurentResidueLinearMap_monomial]
  change (p3HomogeneousDualCoordinateEquiv K d).symm
      (fun b => p3NegativeTwistCohomologyThreeResidueHom K m
        (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
          (p3RawTopCocycleToAugmentedExt K m w)) ⟨b.1, by rw [b.2, hdegree]⟩)
      (p3HomogeneousMonomialBasis K d b) = _
  rw [← p3HomogeneousDualCoordinateEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [p3NegativeTwistCohomologyThreeResidueHom_unit_class,
    p3NegativeTwistAugmentedExtResidueHom_raw]
  rfl

/-- Genuine arbitrary polynomial naturality for the SAME actual intrinsic
Ext class and SAME actual mulHomogeneous. No assumed multiplication square. -/
theorem p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_mulHomogeneous
    [HasExt.{u} (Proj PS).Modules] (m a d : ℕ) (hdegree : a + 4 = m)
    (q : PS d) (b : PS a)
    (z : schemeModuleCohomology (Proj PS) (sheafOfModules PS (m + d)) 3) :
    p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K (m + d) (a + d) (by omega) z
        ⟨(q : MvPolynomial (Fin 4) K) * (b : MvPolynomial (Fin 4) K), by
          simpa only [MvPolynomial.mem_homogeneousSubmodule, Nat.add_comm] using q.2.mul b.2⟩ =
      p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K m a hdegree
        (z.comp (Ext.mk₀ (mulHomogeneous PS q m)) (add_zero 3)) b := by
  let E : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS (m + d)) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS (m + d)) 3 :=
    extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
  obtain ⟨c, rfl⟩ := E.surjective z
  obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K (m + d) c
  dsimp only [E]
  rw [extPrecompIsoOfIso_postcomp, p3RawTopCocycleToAugmentedExt_mulHomogeneous]
  rw [p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_raw,
    p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_raw]
  change (polynomialToLaurent (K := K)
      ((q : MvPolynomial (Fin 4) K) * (b : MvPolynomial (Fin 4) K)) *
      p3NegativeTwistCechTermToLaurent K (m + d) 3 w.1 id).coeff (p3SerreDualExponent 0) =
    (polynomialToLaurent (K := K) (b : MvPolynomial (Fin 4) K) *
      p3NegativeTwistCechTermToLaurent K m 3
        ((p3NegativeTwistCechMultiplication K m d q).f 3 w.1) id).coeff
          (p3SerreDualExponent 0)
  rw [p3NegativeTwistCechMultiplication_toLaurent, map_mul]
  congr 1
  ring

/-- The actual vanishing relation implies genuine annihilation of every
polynomial multiple q*b. This is the precise relation required by the
cubic hypersurface connecting image in the Coray H¹ dimension route. -/
theorem p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_annihilates_multiples
    [HasExt.{u} (Proj PS).Modules] (m a d : ℕ) (hdegree : a + 4 = m)
    (q : PS d)
    (z : schemeModuleCohomology (Proj PS) (sheafOfModules PS (m + d)) 3)
    (hz : z.comp (Ext.mk₀ (mulHomogeneous PS q m)) (add_zero 3) = 0)
    (b : PS a) :
    p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap K (m + d) (a + d) (by omega) z
        ⟨(q : MvPolynomial (Fin 4) K) * (b : MvPolynomial (Fin 4) K), by
          simpa only [MvPolynomial.mem_homogeneousSubmodule, Nat.add_comm] using q.2.mul b.2⟩ = 0 := by
  rw [p3NegativeTwistCohomologyThreeHomogeneousDualLinearMap_mulHomogeneous K m a d hdegree q b z, hz, map_zero]
  rfl

end PfaffianDescent.ProjectiveNegativeTwist
