import PfaffianDescent.ProjectiveLineActualPositiveGlobalSections
import PfaffianDescent.ProjectiveLineNativeBaseScalarValue
import PfaffianDescent.PositiveGradedHomogeneousTopSectionImage
import PfaffianDescent.ActualOpenPullbackAdjunctionChartIso
import PfaffianDescent.HomogeneousDimensions

noncomputable section
namespace PfaffianDescent.ProjectiveLineNative
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "P" => homogeneousSubmodule Bool K
local notation "L" => (⊥ : HomogeneousIdeal P)
local notation "G" => grading L
local notation "A" => CoordinateRing L

/-- Canonical original section structures, with the original scheme index fixed. -/
private noncomputable instance actualLineOpenSectionsAddCommGroup (m : ℕ) :
    AddCommGroup (SchemeModuleOpenSectionsOver (toBase L) (positiveSheafOfModules G m) ⊤) :=
  instAddCommGroupCarrierSchemeModuleOpenSectionsOver
    (K := K) (X := scheme L) (toBase L) (positiveSheafOfModules G m) ⊤

private noncomputable instance actualLineOpenSectionsModule (m : ℕ) :
    Module K (SchemeModuleOpenSectionsOver (toBase L) (positiveSheafOfModules G m) ⊤) :=
  instModuleCarrierSchemeModuleOpenSectionsOver
    (K := K) (X := scheme L) (toBase L) (positiveSheafOfModules G m) ⊤

private noncomputable instance actualLineHZeroAddCommGroup (m : ℕ) :
    AddCommGroup (SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G m)) :=
  instAddCommGroupSchemeModuleGlobalSectionsOver
    (K := K) (X := scheme L) (toBase L) (positiveSheafOfModules G m)

private noncomputable instance actualLineHZeroModule (m : ℕ) :
    Module K (SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G m)) :=
  instModuleSchemeModuleGlobalSectionsOver
    (K := K) (X := scheme L) (toBase L) (positiveSheafOfModules G m)

/-- The literal image homogeneous piece, not an abstract coordinate choice. -/
def actualLineHomogeneousQuotientPiece (m : ℕ) (p : P m) : G m :=
  ⟨quotientGradedRingHom L p, (quotientGradedRingHom L).2 p.2⟩

/-- The graded restriction itself is bijective at the top open, derived
from its actual native pullback Iso and the genuine bottom scheme Iso. -/
theorem actualLinePositiveGradedRestrictionTop_isIso (m : ℕ) :
    IsIso ((gradedRingHomPositiveTwistToPushforward P G
      (quotientGradedRingHom L) (irrelevant_le_map_quotientGradedRingHom L) m).app ⊤) := by
  let q := quotientProjMap L
  letI : IsIso q := (ambientBottomProjectiveIso (R := K) (σ := Bool)).isIso_hom
  have h := actualOpenPullbackAdjunction_chartIso_app_isIso q
    (positiveSheafOfModules P m) (positiveSheafOfModules G m)
    (actualLineBottomPositivePullbackIso K m)
  have hAdj : (Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv
      (positiveSheafOfModules P m) (positiveSheafOfModules G m)
        (actualLineBottomPositivePullbackIso K m).hom =
      gradedRingHomPositiveTwistToPushforward P G (quotientGradedRingHom L)
        (irrelevant_le_map_quotientGradedRingHom L) m := by
    change ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv
      (positiveSheafOfModules P m) (positiveSheafOfModules G m))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv
          (positiveSheafOfModules P m) (positiveSheafOfModules G m)).symm
            (gradedRingHomPositiveTwistToPushforward P G (quotientGradedRingHom L)
              (irrelevant_le_map_quotientGradedRingHom L) m)) = _
    exact ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv
      (positiveSheafOfModules P m) (positiveSheafOfModules G m)).apply_symm_apply _
  rw [hAdj] at h
  have htop : q ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  rw [htop] at h
  exact h

/-- Typed algebraic scalar law before the actual quotient specialization. -/
private lemma nativeAlgHom_smul_eq_mul014
    {R S : Type u} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (c : K) (p : R) :
    f (c • p) = algebraMap K S c * f p :=
  (map_smul f c p).trans (Algebra.smul_def c (f p))

private lemma nativeLocalization_mk_one_mul014
    {R : Type u} [CommRing R] (T : Submonoid R) (a b : R) :
    Localization.mk (a * b) (1 : T) =
      Localization.mk a (1 : T) * Localization.mk b (1 : T) := by
  rw [Localization.mk_mul, one_mul]

/-- The SAME quotient map has the actual canonical original scalar law. -/
private lemma actualLineQuotient_smul_mul014 (m : ℕ) (c : K) (p : P m) :
    quotientGradedRingHom L ((c • p : P m) : MvPolynomial Bool K) =
      algebraMap K A c * quotientGradedRingHom L p := by
  change (Ideal.Quotient.mkₐ K (L).toIdeal) (c • (p : MvPolynomial Bool K)) =
    algebraMap K A c * (Ideal.Quotient.mkₐ K (L).toIdeal) (p : MvPolynomial Bool K)
  exact nativeAlgHom_smul_eq_mul014 K (Ideal.Quotient.mkₐ K (L).toIdeal)
    c (p : MvPolynomial Bool K)

/-- Bounded native base-scalar value on the SAME actual original top open. -/
private lemma actualLineOpenScalar_fraction014 (c : K) (x : ProjectiveSpectrum G) :
    ((schemeOpenBaseRingHom (toBase L) ⊤ c).1 ⟨x, trivial⟩).val =
      Localization.mk (algebraMap K A c) (1 : (positivePointIdeal G x).primeCompl) := by
  rw [schemeOpenBaseRingHom_top_apply]
  change ((affineFunctionHom (actualLineQuotientBaseMap K) c).1 ⟨x, trivial⟩).val = _
  exact actualLineQuotientBaseMap_scalar_value K c x

/-- Literal polynomial sections are linear for the ORIGINAL line structure map. -/
def actualLineLiteralHomogeneousTopSectionLinearMap (m : ℕ) :
    P m →ₗ[K] SchemeModuleOpenSectionsOver (toBase L) (positiveSheafOfModules G m) ⊤ where
  toFun p := PresheafOfModules.sections.eval
    (positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p)) (op ⊤)
  map_add' p q := by
    apply Subtype.ext
    funext x
    change Localization.mk ((quotientGradedRingHom L) ((p : MvPolynomial Bool K) + q))
        (1 : (positivePointIdeal G x.1).primeCompl) =
      Localization.mk (quotientGradedRingHom L p) 1 +
        Localization.mk (quotientGradedRingHom L q) 1
    rw [map_add]
    exact (Localization.add_mk_self (quotientGradedRingHom L p) 1
      (quotientGradedRingHom L q)).symm
  map_smul' c p := by
    apply Subtype.ext
    funext x
    change Localization.mk (quotientGradedRingHom L ((c • p : P m) : MvPolynomial Bool K))
        (1 : (positivePointIdeal G x.1).primeCompl) =
      ((schemeOpenBaseRingHom (toBase L) ⊤ c).1 x).val *
        Localization.mk (quotientGradedRingHom L p) 1
    calc
      _ = Localization.mk (algebraMap K A c * quotientGradedRingHom L p)
          (1 : (positivePointIdeal G x.1).primeCompl) :=
        congrArg (fun z : A => Localization.mk z
          (1 : (positivePointIdeal G x.1).primeCompl))
          (actualLineQuotient_smul_mul014 K m c p)
      _ = Localization.mk (algebraMap K A c) (1 : (positivePointIdeal G x.1).primeCompl) *
          Localization.mk (quotientGradedRingHom L p)
            (1 : (positivePointIdeal G x.1).primeCompl) :=
        nativeLocalization_mk_one_mul014 (positivePointIdeal G x.1).primeCompl
          (algebraMap K A c) (quotientGradedRingHom L p)
      _ = _ := congrArg
        (fun z : Localization (positivePointIdeal G x.1).primeCompl =>
          z * Localization.mk (quotientGradedRingHom L p)
            (1 : (positivePointIdeal G x.1).primeCompl))
        (actualLineOpenScalar_fraction014 K c x.1).symm

/-- Exact literal-section image of the actual graded restriction. -/
theorem actualLineLiteralHomogeneousTopSectionLinearMap_image
    (m : ℕ) (p : P m) :
    actualLineLiteralHomogeneousTopSectionLinearMap K m p =
      (gradedRingHomPositiveTwistToPushforward P G (quotientGradedRingHom L)
        (irrelevant_le_map_quotientGradedRingHom L) m).app ⊤
          (PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous P m p) (op ⊤)) :=
  (positiveGradedHomogeneousTopSectionImage P G (quotientGradedRingHom L)
    (irrelevant_le_map_quotientGradedRingHom L) m p).symm

/-- Bijectivity is derived for the literal map, not inherited from a chosen set transport. -/
theorem actualLineLiteralHomogeneousTopSectionLinearMap_bijective (m : ℕ) :
    Function.Bijective (actualLineLiteralHomogeneousTopSectionLinearMap K m) := by
  let r := (gradedRingHomPositiveTwistToPushforward P G (quotientGradedRingHom L)
    (irrelevant_le_map_quotientGradedRingHom L) m).app ⊤
  letI : IsIso r := actualLinePositiveGradedRestrictionTop_isIso K m
  have hr := ConcreteCategory.bijective_of_isIso r
  let top : P m → Γ(positiveSheafOfModules P m, ⊤) :=
    fun p => PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous P m p) (op ⊤)
  have ht : Function.Bijective top :=
    (schemeModuleSectionsEquivTop (positiveSheafOfModules P m)).bijective.comp
      (ProjectiveFiniteNative.finitePolynomialHomogeneousSectionsEquiv (σ := Bool) K m).bijective
  constructor
  · intro p q h
    apply ht.1
    apply hr.1
    exact (actualLineLiteralHomogeneousTopSectionLinearMap_image K m p).symm.trans
      (h.trans (actualLineLiteralHomogeneousTopSectionLinearMap_image K m q))
  · intro y
    obtain ⟨x, hx⟩ := hr.2 y
    obtain ⟨p, hp⟩ := ht.2 x
    refine ⟨p, ?_⟩
    exact (actualLineLiteralHomogeneousTopSectionLinearMap_image K m p).trans
      ((congrArg r hp).trans hx)

/-- Actual native H0 map, with the original toBase action on the morphism-valued space. -/
def actualLineLiteralHomogeneousHZeroLinearMap (m : ℕ) :
    P m →ₗ[K] SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G m) :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase L) (positiveSheafOfModules G m)).symm.toLinearMap.comp
    (actualLineLiteralHomogeneousTopSectionLinearMap K m)

def actualLineLiteralHomogeneousHZeroLinearEquiv (m : ℕ) :
    P m ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G m) :=
  LinearEquiv.ofBijective (actualLineLiteralHomogeneousHZeroLinearMap K m)
    ((schemeModuleGlobalSectionsLinearEquivOpenTop (toBase L)
      (positiveSheafOfModules G m)).symm.bijective.comp
        (actualLineLiteralHomogeneousTopSectionLinearMap_bijective K m))

/-- The original native H0 inverse is the section inverse after the proved top-section law. -/
private lemma nativeGlobalSectionsLinearTop_symm_section015
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) (M : X.Modules) (s : M.sections) :
    (schemeModuleGlobalSectionsLinearEquivOpenTop π M).symm
        (schemeModuleSectionsEquivTop M s) =
      (schemeModuleGlobalSectionsOverEquivSections π M).symm s := by
  change (schemeModuleGlobalSectionsOverEquivSections π M).symm
      ((schemeModuleSectionsEquivTop M).symm (schemeModuleSectionsEquivTop M s)) = _
  exact congrArg (schemeModuleGlobalSectionsOverEquivSections π M).symm
    ((schemeModuleSectionsEquivTop M).symm_apply_apply s)

/-- Every polynomial, hence each of the four cubic monomials, maps to its
literal quotient-polynomial section in the actual original H0 space. -/
theorem actualLineLiteralHomogeneousHZeroLinearEquiv_apply
    (m : ℕ) (p : P m) :
    actualLineLiteralHomogeneousHZeroLinearEquiv K m p =
      (schemeModuleGlobalSectionsOverEquivSections (toBase L)
        (positiveSheafOfModules G m)).symm
          (positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p)) := by
  change (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase L)
      (positiveSheafOfModules G m)).symm
        (schemeModuleSectionsEquivTop (positiveSheafOfModules G m)
          (positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p))) = _
  exact nativeGlobalSectionsLinearTop_symm_section015 K (toBase L)
    (positiveSheafOfModules G m)
    (positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p))

private lemma actualLineLiteralHomogeneousHZeroLinearEquiv_sections015
    (m : ℕ) (p : P m) :
    schemeModuleGlobalSectionsOverEquivSections (toBase L) (positiveSheafOfModules G m)
        (actualLineLiteralHomogeneousHZeroLinearEquiv K m p) =
      positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p) := by
  let e := schemeModuleGlobalSectionsOverEquivSections (toBase L) (positiveSheafOfModules G m)
  let s := positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p)
  exact (congrArg e (actualLineLiteralHomogeneousHZeroLinearEquiv_apply K m p)).trans
    (e.apply_symm_apply s)

/-- Literal pointwise fraction formula on the original quotient line. -/
theorem actualLineLiteralHomogeneousHZeroLinearEquiv_value
    (m : ℕ) (p : P m) (x : ProjectiveSpectrum G) :
    (positiveSectionValue G m (op ⊤)
      (PresheafOfModules.sections.eval
        (schemeModuleGlobalSectionsOverEquivSections (toBase L) (positiveSheafOfModules G m)
          (actualLineLiteralHomogeneousHZeroLinearEquiv K m p)) (op ⊤)) ⟨x, trivial⟩).1 =
      Localization.mk (quotientGradedRingHom L p : A)
        (1 : (positivePointIdeal G x).primeCompl) := by
  have h := congrArg
    (fun s : (positiveSheafOfModules G m).sections =>
      (positiveSectionValue G m (op ⊤)
        (PresheafOfModules.sections.eval s (op ⊤)) ⟨x, trivial⟩).1)
    (actualLineLiteralHomogeneousHZeroLinearEquiv_sections015 K m p)
  exact h.trans (positiveSectionValue_positiveGlobalSectionOfHomogeneous G m
    (actualLineHomogeneousQuotientPiece K m p) x)

/-- Literal section identity on each original Bool coordinate chart. -/
theorem actualLineLiteralHomogeneousHZeroLinearEquiv_chart
    (m : ℕ) (p : P m) (b : Bool) :
    PresheafOfModules.sections.eval
      (schemeModuleGlobalSectionsOverEquivSections (toBase L) (positiveSheafOfModules G m)
        (actualLineLiteralHomogeneousHZeroLinearEquiv K m p)) (op (quotientCoordinateOpen L b)) =
    PresheafOfModules.sections.eval
      (positiveGlobalSectionOfHomogeneous G m (actualLineHomogeneousQuotientPiece K m p))
        (op (quotientCoordinateOpen L b)) := by
  exact congrArg
    (fun s : (positiveSheafOfModules G m).sections =>
      PresheafOfModules.sections.eval s (op (quotientCoordinateOpen L b)))
    (actualLineLiteralHomogeneousHZeroLinearEquiv_sections015 K m p)

/-- Exact cubic-degree full-section equivalence; all data are original. -/
def actualLineLiteralCubicHZeroLinearEquiv :
    P 3 ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G 3) :=
  actualLineLiteralHomogeneousHZeroLinearEquiv K 3

/-- Actual native H0 has rank m+1 under the ORIGINAL coefficient action.
The native section equivalence, not a polynomial-as-H0 definition, supplies the transport. -/
theorem actualLineLiteralHomogeneousHZero_finrank (m : ℕ) :
    Module.finrank K (SchemeModuleGlobalSectionsOver (toBase L)
      (positiveSheafOfModules G m)) = m + 1 := by
  classical
  rw [← (actualLineLiteralHomogeneousHZeroLinearEquiv K m).finrank_eq]
  let S : Set (Bool →₀ ℕ) := {a | a.degree = m}
  let E : Sym Bool m ≃ S := Sym.equivNatSum Bool m
  letI : Fintype S := Fintype.ofEquiv _ E
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  calc
    _ = Fintype.card S := Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K S)
    _ = Fintype.card (Sym Bool m) := (Fintype.card_congr E).symm
    _ = m + 1 := by
      rw [Sym.card_sym_eq_choose]
      simp only [Fintype.card_bool]
      have h : 2 + m - 1 = m + 1 := by omega
      rw [h]
      exact (Nat.choose_symm_add (a := m) (b := 1)).trans (Nat.choose_one_right _)

/-- In particular, the actual complete cubic section space has dimension four. -/
theorem actualLineLiteralCubicHZero_finite_finrank :
    Module.Finite K (SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G 3)) ∧
    Module.finrank K (SchemeModuleGlobalSectionsOver (toBase L) (positiveSheafOfModules G 3)) = 4 := by
  have h := actualLineLiteralHomogeneousHZero_finrank K 3
  exact ⟨Module.finite_of_finrank_pos (by rw [h]; exact Nat.zero_lt_succ 3), h⟩

end PfaffianDescent.ProjectiveLineNative
end
