import PfaffianDescent.QuarticInfinitesimalPoints
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Geometric splitting of the length-eight dual point

Over an algebraically closed field, the dual-number point attached to a
separable degree-four residue field splits into four dual-number points.
-/

namespace PfaffianDescent
namespace QuarticNet

open Module
open scoped TensorProduct

universe u

theorem etale_splits_over_algClosed (K A : Type u) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Algebra.Etale K A] :
    ∃ (I : Type u) (_ : Fintype I), Nonempty (A ≃ₐ[K] (I → K)) := by
  classical
  obtain ⟨I, hI, Ai, hfields, halgs, e, hfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI := hI
  letI := Fintype.ofFinite I
  letI := hfields
  letI := halgs
  have heach (i : I) : Nonempty (Ai i ≃ₐ[K] K) := by
    haveI := (hfinite i).1
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId K (Ai i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩
  exact ⟨I, inferInstance, ⟨e.trans (AlgEquiv.piCongrRight (fun i => (heach i).some))⟩⟩

theorem separable_baseChange_splits (k K L : Type u) [Field k] [Field K] [Field L]
    [IsAlgClosed K] [Algebra k K] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ (I : Type u) (_ : Fintype I),
      Fintype.card I = Module.finrank k L ∧ Nonempty ((K ⊗[k] L) ≃ₐ[K] (I → K)) := by
  haveI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  haveI : Algebra.Etale k L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := etale_splits_over_algClosed K (K ⊗[k] L)
  letI := hI
  refine ⟨I, hI, ?_, ⟨e⟩⟩
  have hd := e.toLinearEquiv.finrank_eq
  simpa [Module.finrank_baseChange, Module.finrank_pi, finrank_self] using hd.symm

noncomputable def dualNumberBaseChange (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] :
    (K ⊗[k] DualNumber L) ≃ₐ[K] DualNumber (K ⊗[k] L) := by
  let e : (K ⊗[k] DualNumber L) ≃ₗ[K] DualNumber (K ⊗[k] L) :=
    TensorProduct.prodRight k K K L L
  have ht (a : K) (b : DualNumber L) :
      e (a ⊗ₜ[k] b) = (a ⊗ₜ[k] b.fst, a ⊗ₜ[k] b.snd) := rfl
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · rw [Algebra.TensorProduct.one_def, ht]
    apply TrivSqZeroExt.ext <;> simp [Algebra.TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    intro a c b d
    change e ((a * c) ⊗ₜ[k] (b * d)) = e (a ⊗ₜ[k] b) * e (c ⊗ₜ[k] d)
    rw [ht, ht, ht]
    apply TrivSqZeroExt.ext
    · change (a * c) ⊗ₜ[k] (b.fst * d.fst) =
        (a ⊗ₜ[k] b.fst) * (c ⊗ₜ[k] d.fst)
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    · change (a * c) ⊗ₜ[k] (b.fst * d.snd + b.snd * d.fst) =
        (a ⊗ₜ[k] b.fst) * (c ⊗ₜ[k] d.snd) +
          (a ⊗ₜ[k] b.snd) * (c ⊗ₜ[k] d.fst)
      rw [TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]

noncomputable def dualNumberCongr {K A B : Type u} [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    DualNumber A ≃ₐ[K] DualNumber B where
  toFun x := TrivSqZeroExt.inl (e x.fst) + TrivSqZeroExt.inr (e x.snd)
  invFun x := TrivSqZeroExt.inl (e.symm x.fst) + TrivSqZeroExt.inr (e.symm x.snd)
  left_inv x := by apply TrivSqZeroExt.ext <;> simp
  right_inv x := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by apply TrivSqZeroExt.ext <;> simp [DualNumber.snd_mul]
  commutes' c := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

noncomputable def dualNumberPi (K I : Type u) [Field K] :
    DualNumber (I → K) ≃ₐ[K] (I → DualNumber K) where
  toFun x i := (x.fst i, x.snd i)
  invFun f := (fun i => (f i).fst, fun i => (f i).snd)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem degree_four_dualPoint_splits (k K L : Type u) [Field k] [Field K] [Field L]
    [IsAlgClosed K] [Algebra k K] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] (hL : Module.finrank k L = 4) :
    ∃ (I : Type u) (_ : Fintype I), Fintype.card I = 4 ∧
      Nonempty ((K ⊗[k] DualNumber L) ≃ₐ[K] (I → DualNumber K)) := by
  obtain ⟨I, hI, hc, ⟨e⟩⟩ := separable_baseChange_splits k K L
  exact ⟨I, hI, hc.trans hL, ⟨(dualNumberBaseChange k K L).trans
    ((dualNumberCongr e).trans (dualNumberPi K I))⟩⟩

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
theorem degree_four_dualPoint_scheme_splits (k K L : Type u)
    [Field k] [Field K] [Field L] [IsAlgClosed K] [Algebra k K] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] (hL : Module.finrank k L = 4) :
    ∃ (I : Type u) (_ : Fintype I), Fintype.card I = 4 ∧
      Nonempty (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber L)))) ≅
        ∐ fun _ : I => Spec (.of (DualNumber K))) := by
  obtain ⟨I, hI, hc, ⟨e⟩⟩ := degree_four_dualPoint_splits k K L hL
  letI := hI
  refine ⟨I, hI, hc, ⟨?_⟩⟩
  exact (pullbackSpecIso k K (DualNumber L)) ≪≫
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op ≪≫
    (asIso (sigmaSpec (fun _ : I => CommRingCat.of (DualNumber K)))).symm

end QuarticNet
end PfaffianDescent
