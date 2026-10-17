import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Group.Units.Hom

/-! SOURCE ONLY176. Native differential transport through a genuine
algebra homomorphism, including inverse-unit-scaled coordinate forms. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]

/-- Native map Ω[A/K] → Ω[B/K], with the scalar action induced by f. -/
def nativeKaehlerMapAlongAlgHom176 (f : A →ₐ[K] B) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    KaehlerDifferential K A →ₗ[A] KaehlerDifferential K B := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower K A B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.map K K A B

theorem nativeKaehlerMapAlongAlgHom_D176 (f : A →ₐ[K] B) (x : A) :
    nativeKaehlerMapAlongAlgHom176 f (KaehlerDifferential.D K A x) =
      KaehlerDifferential.D K B (f x) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower K A B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.map_D K K A B x

/-- A genuine inverse-unit differential transports to the same expression
with the mapped unit and actual mapped coordinate. -/
theorem nativeKaehlerMapAlongAlgHom_inverseUnit_D176
    (f : A →ₐ[K] B) (a : Aˣ) (x : A) :
    nativeKaehlerMapAlongAlgHom176 f
      (((a⁻¹ : Aˣ) : A) • KaehlerDifferential.D K A x) =
      (((Units.map f.toRingHom.toMonoidHom a)⁻¹ : Bˣ) : B) •
        KaehlerDifferential.D K B (f x) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  rw [map_smul, nativeKaehlerMapAlongAlgHom_D176]
  rfl

end PfaffianDescent.Coray
