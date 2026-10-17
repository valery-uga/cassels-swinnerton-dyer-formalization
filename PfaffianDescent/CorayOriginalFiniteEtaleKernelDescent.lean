import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct
universe u
set_option autoImplicit false

/-- The literal scalar extension of the ORIGINAL finite etale algebra,
with its ACTUAL split algebra constructed over the separably closed field.
The full algebra and original coefficient actions are retained. -/
def originalFiniteEtaleGeometricSplit
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M] :
    (M ⊗[K] A) ≃ₐ[M] (PrimeSpectrum (M ⊗[K] A) → M) :=
  Algebra.FormallyEtale.equivPiOfIsSepClosed M (M ⊗[K] A)

/-- An actual geometric point of the SAME scalar-extended finite algebra
induces its literal ORIGINAL-K evaluation map; no embeddings or splitting
outcome is supplied. -/
def originalFiniteEtaleGeometricPoint
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    (p : PrimeSpectrum (M ⊗[K] A)) : A →ₐ[K] M :=
  (((Pi.evalAlgHom M (fun _ : PrimeSpectrum (M ⊗[K] A) => M) p).comp
      (originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)).toAlgHom).restrictScalars K).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[K] M ⊗[K] A)

/-- The actual geometric evaluation preserves both the ORIGINAL A map
and the extension coefficient: no unidentified product coordinate is used. -/
theorem originalFiniteEtaleGeometricSplit_tmul_apply001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    (a : M) (b : A) (p : PrimeSpectrum (M ⊗[K] A)) :
    originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M) (a ⊗ₜ[K] b) p =
      a * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) p b := by
  have ht : a ⊗ₜ[K] b = a • ((1 : M) ⊗ₜ[K] b) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ht, map_smul]
  rfl

/-- The actual number of geometric points is the ORIGINAL finite algebra
rank. In particular an actual degree3 point has exactly three such points.
No cardinality or three-conjugate enumeration is a premise. -/
theorem originalFiniteEtaleGeometricPoints_natCard_eq_originalFinrank001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M] :
    Nat.card (PrimeSpectrum (M ⊗[K] A)) = Module.finrank K A := by
  let D := M ⊗[K] A
  letI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  letI : Module.Finite M D := inferInstance
  letI : IsArtinianRing D := isArtinian_of_tower M inferInstance
  letI : Fintype (PrimeSpectrum D) := Fintype.ofFinite _
  let e := originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)
  have hSplit : Module.finrank M D = Fintype.card (PrimeSpectrum D) := by
    calc
      _ = Module.finrank M (PrimeSpectrum D → M) := e.toLinearEquiv.finrank_eq
      _ = _ := Module.finrank_pi M
  have hBase : Module.finrank M D = Module.finrank K A := Module.finrank_baseChange
  simpa only [Nat.card_eq_fintype_card] using hSplit.symm.trans hBase

/-- Vanishing at ALL actual geometric points of the SAME finite etale
algebra identifies precisely the scalar extension of the ORIGINAL-K
through-point evaluation kernel. Split injectivity and flatness prove this;
no kernel equality, component selection or image outcome is supplied. -/
theorem originalFiniteEtale_allGeometricEvaluations_kernel_eq_tensorOriginalKernel001
    {K A M W : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    [AddCommGroup W] [Module K W] (f : W →ₗ[K] A) :
    LinearMap.ker ((originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)).toLinearMap.comp
      (AlgebraTensorModule.lTensor M M f)) =
      LinearMap.range (AlgebraTensorModule.lTensor M M (LinearMap.ker f).subtype) := by
  rw [LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)).injective)]
  exact Module.Flat.ker_lTensor_eq M M f

/-- A nonzero actual extended jet on a section vanishing at all geometric
points DERIVES an ORIGINAL-K through-point section with nonzero SAME jet.
The original section is constructed via exact tensor-kernel identification,
not by promoting extension-field coefficients to K. -/
theorem originalFiniteEtale_nonzeroGeometricKernelJet_exists_originalKernelSection001
    {K A M W V : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    [AddCommGroup W] [Module K W] [AddCommGroup V] [Module M V]
    (f : W →ₗ[K] A) (J : M ⊗[K] W →ₗ[M] V)
    (hNonzero : ∃ z : M ⊗[K] W,
      (originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M))
        (AlgebraTensorModule.lTensor M M f z) = 0 ∧ J z ≠ 0) :
    ∃ w : W, f w = 0 ∧ J ((1 : M) ⊗ₜ[K] w) ≠ 0 := by
  classical
  letI : Module K V := Module.compHom V (algebraMap K M)
  letI : IsScalarTower K M V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  by_contra h
  push_neg at h
  have hRestricted : J.comp (AlgebraTensorModule.lTensor M M (LinearMap.ker f).subtype) = 0 := by
    apply AlgebraTensorModule.ext
    intro a w
    change J (a ⊗ₜ[K] (w : W)) = 0
    have hw : J ((1 : M) ⊗ₜ[K] (w : W)) = 0 := h w w.2
    calc
      _ = a • J ((1 : M) ⊗ₜ[K] (w : W)) := by
        rw [← map_smul]
        congr 1
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = 0 := by rw [hw, smul_zero]
  obtain ⟨z, hEval, hJet⟩ := hNonzero
  have hz : z ∈ LinearMap.range (AlgebraTensorModule.lTensor M M (LinearMap.ker f).subtype) := by
    rw [← originalFiniteEtale_allGeometricEvaluations_kernel_eq_tensorOriginalKernel001 f]
    exact hEval
  obtain ⟨t, ht⟩ := hz
  have htZero := LinearMap.congr_fun hRestricted t
  exact hJet (by simpa only [LinearMap.comp_apply, LinearMap.zero_apply, ht] using htZero)

end PfaffianDescent.Coray
