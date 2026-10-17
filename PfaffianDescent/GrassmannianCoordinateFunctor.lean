import PfaffianDescent.GrassmannianQuotientBaseChange
import PfaffianDescent.GrassmannianLocalNaturality

namespace PfaffianDescent
open CategoryTheory
universe u
section
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {m n : ℕ}

lemma grassmannianSubmoduleBaseChange_id (W : Submodule R ((Fin m → R) × (Fin n → R))) :
    grassmannianSubmoduleBaseChange (RingHom.id R) W = W := by
  have he : (graphCoefficientMap (m := m) (n := n) (RingHom.id R) : _ → _) = id := rfl
  rw [grassmannianSubmoduleBaseChange, he, Set.image_id, Submodule.span_eq]

lemma grassmannianSubmoduleBaseChange_comp (φ : R →+* S) (ψ : S →+* T)
    (W : Submodule R ((Fin m → R) × (Fin n → R))) :
    grassmannianSubmoduleBaseChange ψ (grassmannianSubmoduleBaseChange φ W) =
      grassmannianSubmoduleBaseChange (ψ.comp φ) W := by
  rw [grassmannianSubmoduleBaseChange, grassmannianSubmoduleBaseChange,
    span_image_span_semilinear, ← Set.image_comp]
  rfl

/-- Base change of a locally free coordinate quotient under an arbitrary ring homomorphism. -/
noncomputable def grassmannianQuotientMap (φ : R →+* S)
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    Module.Grassmannian S ((Fin m → S) × (Fin n → S)) n := by
  letI : Algebra R S := φ.toAlgebra
  exact grassmannianQuotientBaseChange R S W

lemma grassmannianQuotientMap_submodule (φ : R →+* S)
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    (grassmannianQuotientMap φ W).toSubmodule = grassmannianSubmoduleBaseChange φ W.toSubmodule := rfl

lemma grassmannianQuotientMap_id (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    grassmannianQuotientMap (RingHom.id R) W = W := by
  apply Module.Grassmannian.ext
  exact grassmannianSubmoduleBaseChange_id W.toSubmodule

lemma grassmannianQuotientMap_comp (φ : R →+* S) (ψ : S →+* T)
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    grassmannianQuotientMap (ψ.comp φ) W = grassmannianQuotientMap ψ (grassmannianQuotientMap φ W) := by
  apply Module.Grassmannian.ext
  exact (grassmannianSubmoduleBaseChange_comp φ ψ W.toSubmodule).symm

end
section
variable (K : Type u) [CommRing K] (m n : ℕ)

/-- The full quotient Grassmannian functor in ambient coordinates. -/
noncomputable def grassmannianCoordinateFunctor : CommAlgCat.{u, u} K ⥤ Type u where
  obj A := Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n
  map φ := ↾(grassmannianQuotientMap φ.hom.toRingHom)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro W
    exact grassmannianQuotientMap_id W
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro W
    exact grassmannianQuotientMap_comp φ.hom.toRingHom ψ.hom.toRingHom W

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [IsLocalRing A] [IsLocalRing B]

/-- The local point correspondence commutes with actual tensor-product quotient base change. -/
lemma grassmannianLocalModuliEquiv_baseChange (φ : A →ₐ[K] B) (p : GrassmannianAlgebraPoint K A m n) :
    grassmannianLocalModuliEquiv K B m n (grassmannianAlgebraPointMap K φ m n p) =
      grassmannianQuotientMap φ.toRingHom (grassmannianLocalModuliEquiv K A m n p) := by
  apply Module.Grassmannian.ext
  exact grassmannianLocalModuliEquiv_naturality K φ m n p

end
end PfaffianDescent
