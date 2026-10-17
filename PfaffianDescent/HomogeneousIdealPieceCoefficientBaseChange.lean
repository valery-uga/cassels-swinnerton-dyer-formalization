import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.HomogeneousCoefficientDescent
import PfaffianDescent.ProjectiveLinearSystem

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Coefficient extension on a homogeneous polynomial component, viewed as a
linear map over the ground field. -/
noncomputable def homogeneousIdealPieceAmbientCoefficientMap (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) k d →ₗ[k]
      MvPolynomial.homogeneousSubmodule (Fin 4) K d where
  toFun := fun p => ⟨MvPolynomial.map (algebraMap k K) p.val, p.property.map _⟩
  map_add' := by
    intro p q
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' := by
    intro a p
    apply Subtype.ext
    change MvPolynomial.map (algebraMap k K) (a • p.val) =
      a • MvPolynomial.map (algebraMap k K) p.val
    calc
      MvPolynomial.map (algebraMap k K) (a • p.val) =
          (algebraMap k K a) • MvPolynomial.map (algebraMap k K) p.val := by
        simp only [smul_eq_C_mul, map_mul, map_C]
      _ = a • MvPolynomial.map (algebraMap k K) p.val :=
        IsScalarTower.algebraMap_smul K a _

/-- Coefficient extension on the degree-`d` part of a homogeneous ideal. -/
noncomputable def homogeneousIdealPieceCoefficientMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d : ℕ) : homogeneousIdealPiece I d →ₗ[k] homogeneousIdealPiece J d where
  toFun := fun p => ⟨homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d p.val, by
    change MvPolynomial.map (algebraMap k K) p.val.val ∈ J.toIdeal
    rw [← hIJ]
    exact Ideal.mem_map_of_mem _ p.property⟩
  map_add' := by
    intro p q
    apply Subtype.ext
    exact (homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d).map_add p.val q.val
  map_smul' := by
    intro a p
    apply Subtype.ext
    exact (homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d).map_smul a p.val

theorem homogeneousIdealPieceCoefficientMap_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d : ℕ) :
    Function.Injective (homogeneousIdealPieceCoefficientMap I J hIJ d) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  apply MvPolynomial.map_injective (algebraMap k K)
    (FaithfulSMul.algebraMap_injective k K)
  exact congrArg (fun r : homogeneousIdealPiece J d => r.val.val) hpq

end PfaffianDescent


namespace PfaffianDescent

open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

noncomputable def homogeneousIdealPieceAmbientCoefficientTensorMap (d : ℕ) :
    K ⊗[k] MvPolynomial.homogeneousSubmodule (Fin 4) k d →ₗ[K]
      MvPolynomial.homogeneousSubmodule (Fin 4) K d :=
  LinearMap.liftBaseChange K (homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d)

theorem homogeneousIdealPieceAmbientCoefficientTensorMap_surjective (d : ℕ) :
    Function.Surjective
      (homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d) := by
  intro p
  let q : Monomials (Fin 4) d → MvPolynomial.homogeneousSubmodule (Fin 4) k d :=
    fun m => ⟨MvPolynomial.monomial m.val 1, MvPolynomial.isHomogeneous_monomial _ m.property⟩
  let z : K ⊗[k] MvPolynomial.homogeneousSubmodule (Fin 4) k d :=
    ∑ m : Monomials (Fin 4) d, p.val.coeff m.val ⊗ₜ q m
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change ((homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d)
      (∑ m : Monomials (Fin 4) d, p.val.coeff m.val ⊗ₜ q m)).val = p.val
  rw [map_sum]
  simp only [homogeneousIdealPieceAmbientCoefficientTensorMap, LinearMap.liftBaseChange_tmul]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change ∑ m : Monomials (Fin 4) d, p.val.coeff m.val •
      (homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d (q m)).val = p.val
  dsimp [homogeneousIdealPieceAmbientCoefficientMap, q]
  simp only [MvPolynomial.map_monomial, map_one]
  rw [show (fun m : Monomials (Fin 4) d => p.val.coeff m.val •
      MvPolynomial.monomial m.val (1 : K)) = fun m =>
        MvPolynomial.monomial m.val (p.val.coeff m.val) by
      funext m
      rw [MvPolynomial.smul_monomial]
      simp]
  exact sum_monomial_coeff_eq p.val p.property

theorem homogeneousIdealPieceAmbientCoefficientTensorMap_bijective (d : ℕ) :
    Function.Bijective
      (homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d) := by
  let Hk := MvPolynomial.homogeneousSubmodule (Fin 4) k d
  let HK := MvPolynomial.homogeneousSubmodule (Fin 4) K d
  letI : FiniteDimensional k Hk :=
    (Submodule.fg_iff_finiteDimensional Hk).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) k d)
  letI : Module.Free k Hk := Module.Free.of_divisionRing k Hk
  letI : FiniteDimensional K HK :=
    (Submodule.fg_iff_finiteDimensional HK).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K d)
  have hfinrank : Module.finrank K (K ⊗[k] Hk) = Module.finrank K HK := by
    calc
      Module.finrank K (K ⊗[k] Hk) = Module.finrank k Hk :=
        Module.finrank_baseChange (R := K) (S := k) (M' := Hk)
      _ = (d + 3).choose 3 := four_variable_homogeneous_finrank d
      _ = Module.finrank K HK := (four_variable_homogeneous_finrank d).symm
  have hsurj : Function.Surjective
      (homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d) :=
    homogeneousIdealPieceAmbientCoefficientTensorMap_surjective d
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mpr hsurj, hsurj⟩

end PfaffianDescent


namespace PfaffianDescent

open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Scalar extension of the coefficient map on a homogeneous ideal piece. -/
noncomputable def homogeneousIdealPieceCoefficientTensorMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d : ℕ) : K ⊗[k] homogeneousIdealPiece I d →ₗ[K] homogeneousIdealPiece J d :=
  LinearMap.liftBaseChange K (homogeneousIdealPieceCoefficientMap I J hIJ d)

theorem homogeneousIdealPieceCoefficientTensorMap_subtype_comp
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d : ℕ) :
    ((homogeneousIdealPiece J d).subtype).comp
      (homogeneousIdealPieceCoefficientTensorMap I J hIJ d) =
      (homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d).comp
        (AlgebraTensorModule.lTensor K K (homogeneousIdealPiece I d).subtype) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
    apply Subtype.ext
    change (a • homogeneousIdealPieceCoefficientMap I J hIJ d x).val =
      ((homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d)
        (a ⊗ₜ x.val)).val
    change (a • homogeneousIdealPieceCoefficientMap I J hIJ d x).val =
      ((LinearMap.liftBaseChange K
        (homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d))
          (a ⊗ₜ x.val)).val
    rw [LinearMap.liftBaseChange_tmul]
    rfl


end PfaffianDescent


namespace PfaffianDescent

open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

theorem homogeneousIdealPieceCoefficientTensorMap_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d : ℕ) :
    Function.Injective (homogeneousIdealPieceCoefficientTensorMap I J hIJ d) := by
  have hsub : Function.Injective
      (AlgebraTensorModule.lTensor K K (homogeneousIdealPiece I d).subtype) := by
    let P := homogeneousIdealPiece I d
    let H := MvPolynomial.homogeneousSubmodule (Fin 4) k d
    let f : P →ₗ[k] H := P.subtype
    have hf : Function.Injective f := P.subtype_injective
    have hker : LinearMap.ker f = ⊥ := by
      ext x
      constructor
      · intro hx
        have hx0 : x = 0 := hf (by simpa using hx)
        simp [hx0]
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        simp [hx0]
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      (K := k) (V := P) (V' := H) f hker
    let L : K ⊗[k] P →ₗ[K] K ⊗[k] H := AlgebraTensorModule.lTensor K K f
    let R : K ⊗[k] H →ₗ[K] K ⊗[k] P := AlgebraTensorModule.lTensor K K g
    have hcomp : R.comp L = LinearMap.id := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul a x =>
        rw [LinearMap.comp_apply, AlgebraTensorModule.lTensor_tmul,
          AlgebraTensorModule.lTensor_tmul]
        congr 1
        exact LinearMap.congr_fun hg x
    have hL : Function.Injective L := by
      intro x y hxy
      calc
        x = (LinearMap.id : K ⊗[k] P →ₗ[K] K ⊗[k] P) x := rfl
        _ = (R.comp L) x := by rw [hcomp]
        _ = (R.comp L) y := congrArg R hxy
        _ = (LinearMap.id : K ⊗[k] P →ₗ[K] K ⊗[k] P) y := by rw [hcomp]
        _ = y := rfl
    exact hL
  have hambient : Function.Injective
      (homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d) :=
    (homogeneousIdealPieceAmbientCoefficientTensorMap_bijective (k := k) (K := K) d).1
  have hcomp : Function.Injective
      (((homogeneousIdealPiece J d).subtype).comp
        (homogeneousIdealPieceCoefficientTensorMap I J hIJ d)) := by
    rw [homogeneousIdealPieceCoefficientTensorMap_subtype_comp]
    exact hambient.comp hsub
  intro x y hxy
  apply hcomp
  simp only [LinearMap.comp_apply, hxy]

end PfaffianDescent


namespace PfaffianDescent

open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

theorem homogeneousIdealPiece_finrank_le_coefficientExtension
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d : ℕ) :
    Module.finrank k (homogeneousIdealPiece I d) ≤
      Module.finrank K (homogeneousIdealPiece J d) := by
  let Pk := homogeneousIdealPiece I d
  let PK := homogeneousIdealPiece J d
  let HK := MvPolynomial.homogeneousSubmodule (Fin 4) K d
  letI : FiniteDimensional k Pk := inferInstance
  letI : Module.Free k Pk := Module.Free.of_divisionRing k Pk
  letI : FiniteDimensional K HK :=
    (Submodule.fg_iff_finiteDimensional HK).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K d)
  letI : FiniteDimensional K PK := inferInstance
  rw [← Module.finrank_baseChange (R := K) (S := k) (M' := Pk)]
  exact LinearMap.finrank_le_finrank_of_injective
    (homogeneousIdealPieceCoefficientTensorMap_injective I J hIJ d)

end PfaffianDescent


namespace PfaffianDescent

open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Equal dimensions promote scalar extension of a homogeneous ideal piece to
an isomorphism. -/
theorem homogeneousIdealPieceCoefficientTensorMap_bijective_of_finrank_eq
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (d n : ℕ)
    (hI : Module.finrank k (homogeneousIdealPiece I d) = n)
    (hJ : Module.finrank K (homogeneousIdealPiece J d) = n) :
    Function.Bijective (homogeneousIdealPieceCoefficientTensorMap I J hIJ d) := by
  let Pk := homogeneousIdealPiece I d
  let PK := homogeneousIdealPiece J d
  let HK := MvPolynomial.homogeneousSubmodule (Fin 4) K d
  letI : FiniteDimensional k Pk := inferInstance
  letI : Module.Free k Pk := Module.Free.of_divisionRing k Pk
  letI : FiniteDimensional K HK :=
    (Submodule.fg_iff_finiteDimensional HK).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K d)
  letI : FiniteDimensional K PK := inferInstance
  have hfinrank : Module.finrank K (K ⊗[k] Pk) = Module.finrank K PK := by
    calc
      Module.finrank K (K ⊗[k] Pk) = Module.finrank k Pk :=
        Module.finrank_baseChange (R := K) (S := k) (M' := Pk)
      _ = n := hI
      _ = Module.finrank K PK := hJ.symm
  have hinj : Function.Injective (homogeneousIdealPieceCoefficientTensorMap I J hIJ d) :=
    homogeneousIdealPieceCoefficientTensorMap_injective I J hIJ d
  have hsurj : Function.Surjective (homogeneousIdealPieceCoefficientTensorMap I J hIJ d) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := K ⊗[k] Pk) (V₂ := PK) hfinrank
      (f := homogeneousIdealPieceCoefficientTensorMap I J hIJ d)).mp hinj
  exact ⟨hinj, hsurj⟩

end PfaffianDescent
