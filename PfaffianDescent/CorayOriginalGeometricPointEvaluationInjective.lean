import PfaffianDescent.CorayOriginalFiniteEtaleKernelDescent

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct
universe u
set_option autoImplicit false

/-- Distinct ACTUAL geometric points of the SAME finite etale algebra have
distinct ORIGINAL-K evaluation homs. The actual split product and tensor
compatibility PROVE injectivity; no embedding/distinctness certificate. -/
theorem originalFiniteEtaleGeometricPoint_injective001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M] :
    Function.Injective (originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M)) := by
  classical
  intro p q hPoint
  by_contra hpq
  let e := originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)
  have hEval (z : M ⊗[K] A) : e z p = e z q := by
    change originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M) z p =
      originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M) z q
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; rfl
    | tmul a b =>
      rw [originalFiniteEtaleGeometricSplit_tmul_apply001,
        originalFiniteEtaleGeometricSplit_tmul_apply001, AlgHom.congr_fun hPoint b]
    | add z w hz hw => simp only [map_add, Pi.add_apply, hz, hw]
  let z := e.symm (Pi.single p (1 : M))
  have hImage : e z = Pi.single p (1 : M) := e.apply_symm_apply _
  have h := hEval z
  rw [hImage] at h
  have hOneZero : (1 : M) = 0 := by simpa [Pi.single_apply, Ne.symm hpq] using h
  exact one_ne_zero hOneZero

end PfaffianDescent.Coray
