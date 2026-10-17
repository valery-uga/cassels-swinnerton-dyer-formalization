import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Basis

namespace PfaffianDescent
open CategoryTheory ModuleCat Module
open scoped TensorProduct ChangeOfRings
section
variable {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    {M N : ModuleCat R} {ι κ : Type*}

/-- A basis after extension of scalars, expressed using the categorical functor. -/
noncomputable def scalarExtensionBasis (b : Basis ι R M) :
    Basis ι T ((extendScalars f).obj M) := by
  letI := f.toAlgebra
  exact b.baseChange T

lemma scalarExtensionBasis_apply (b : Basis ι R M) (i : ι) :
    scalarExtensionBasis f b i = (1 : T) ⊗ₜ[R,f] b i := by
  letI := f.toAlgebra
  exact Basis.baseChange_apply T b i

lemma scalarExtensionBasis_repr (b : Basis ι R M) (t : T) (m : M) (i : ι) :
    (scalarExtensionBasis f b).repr (t ⊗ₜ[R,f] m) i = f (b.repr m i) * t := by
  letI := f.toAlgebra
  exact Basis.baseChange_repr_tmul T b t m i

/-- If every coefficient of a linear map vanishes in the target ring, its
extension of scalars is the zero map. -/
theorem scalarExtension_map_zero (b : Basis ι R M) (c : Basis κ R N) (g : M ⟶ N)
    (hg : ∀ i j, f (c.repr (g (b i)) j) = 0) : (extendScalars f).map g = 0 := by
  apply ModuleCat.hom_ext
  apply (scalarExtensionBasis f b).ext
  intro i
  apply (scalarExtensionBasis f c).repr.injective
  ext j
  change (scalarExtensionBasis f c).repr (((extendScalars f).map g) (scalarExtensionBasis f b i)) j = 0
  have he : ((extendScalars f).map g) (scalarExtensionBasis f b i) =
      (1 : T) ⊗ₜ[R,f] g (b i) :=
    (congrArg ((extendScalars f).map g) (scalarExtensionBasis_apply f b i)).trans
      (ExtendScalars.map_tmul f g 1 (b i))
  exact (congrArg (fun v : (extendScalars f).obj N =>
    (scalarExtensionBasis f c).repr v j) he).trans
      ((scalarExtensionBasis_repr f c 1 (g (b i)) j).trans (by rw [hg, zero_mul]))

/-- Extension of scalars preserves addition of module morphisms. -/
instance scalarExtension_additive : (extendScalars f).Additive where
  map_add {X Y} g h := by
    letI := f.toAlgebra
    apply ExtendScalars.hom_ext
    intro m
    change (1 : T) ⊗ₜ[R,f] (g m + h m) =
      (1 : T) ⊗ₜ[R,f] g m + (1 : T) ⊗ₜ[R,f] h m
    exact TensorProduct.tmul_add _ _ _

end
end PfaffianDescent
