import Mathlib.FieldTheory.Fixed
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import PfaffianDescent.FiniteSchemeAlgebra
import Mathlib.RingTheory.Etale.Pi
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Splitting a finite algebra by a full set of rational points

Distinct algebra maps to the ground field are linearly independent as
characters. If their number equals the vector-space rank of the algebra,
evaluation at those maps identifies the algebra with the corresponding
product of copies of the ground field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Module

universe u v

/-- A finite `K`-algebra with as many distinct `K`-points as its rank is
already the product algebra on those points. -/
theorem finiteAlgebra_eval_bijective_of_full_rational_points
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    {n : ℕ} (f : Fin n → A →ₐ[K] K) (hf : Function.Injective f)
    (hn : Module.finrank K A = n) :
    Function.Bijective (AlgHom.pi f : A →ₐ[K] (Fin n → K)) := by
  let g : A →ₐ[K] (Fin n → K) := AlgHom.pi f
  have hli : LinearIndependent K (fun i => (f i).toLinearMap) :=
    (linearIndependent_toLinearMap K A K).comp f hf
  have hdim : Module.finrank K (Module.Dual K A) = n := by
    rw [Subspace.dual_finrank_eq, hn]
  have hspan : Submodule.span K
      (Set.range (fun i => (f i).toLinearMap)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simpa [hdim])
  have hinj : Function.Injective g := by
    intro x y hxy
    have hzero : x - y = 0 := by
      apply (Module.eval_apply_eq_zero_iff K (x - y)).mp
      apply LinearMap.ext_on_range hspan
      intro i
      have hi := congrFun hxy i
      change f i x = f i y at hi
      simpa using sub_eq_zero.mpr hi
    exact sub_eq_zero.mp hzero
  have hfin : Module.finrank K (Fin n → K) = n := by
    simp
  have hsurj : Function.Surjective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hn.trans hfin.symm) (f := g.toLinearMap)).mp hinj
  exact ⟨hinj, hsurj⟩

/-- The point-evaluation map is an algebra equivalence once the number of
distinct rational points exhausts the algebra rank. -/
noncomputable def finiteAlgebra_equiv_pi_of_full_rational_points
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    {n : ℕ} (f : Fin n → A →ₐ[K] K) (hf : Function.Injective f)
    (hn : Module.finrank K A = n) : A ≃ₐ[K] (Fin n → K) :=
  AlgEquiv.ofBijective (AlgHom.pi f)
    (finiteAlgebra_eval_bijective_of_full_rational_points f hf hn)

/-- In particular, a full set of distinct rational points forces the
finite algebra to be reduced. -/
theorem finiteAlgebra_isReduced_of_full_rational_points
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    {n : ℕ} (f : Fin n → A →ₐ[K] K) (hf : Function.Injective f)
    (hn : Module.finrank K A = n) : IsReduced A := by
  exact isReduced_of_injective (AlgHom.pi f)
    (finiteAlgebra_eval_bijective_of_full_rational_points f hf hn).1

/-- If a finite scheme of rank `n` over a field has `n` distinct rational
sections, its actual global coordinate algebra is the product `K^n`. -/
noncomputable def finiteSchemeCoefficient_equiv_pi_of_full_rational_points
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    {n : ℕ} (x : Fin n → (Spec (.of K) ⟶ X))
    (hxbase : ∀ i, x i ≫ f =
      Spec.map (CommRingCat.ofHom (RingHom.id K)))
    (hxinj : Function.Injective x)
    (hrank : AllCharacteristics.finiteSchemeRank f = n) :
    letI := finiteSchemeCoefficientAlgebra f
    Γ(X, ⊤) ≃ₐ[K] (Fin n → K) := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI : Algebra K K := (RingHom.id K).toAlgebra
  let e : Fin n → Γ(X, ⊤) →ₐ[K] K :=
    fun i => finiteSchemePointAlgHom f (x i) (RingHom.id K) (hxbase i)
  have heinj : Function.Injective e := by
    intro i j hij
    have hi := finiteSchemePointAlgHom_spec f (x i) (RingHom.id K) (hxbase i)
    have hj := finiteSchemePointAlgHom_spec f (x j) (RingHom.id K) (hxbase j)
    have hspec : x i ≫ X.isoSpec.hom = x j ≫ X.isoSpec.hom := by
      rw [← hi, ← hj]
      exact congrArg (fun h : Γ(X, ⊤) →ₐ[K] K =>
        Spec.map (CommRingCat.ofHom h.toRingHom)) hij
    apply hxinj
    have := congrArg (fun g : Spec (.of K) ⟶ Spec (.of Γ(X, ⊤)) =>
      g ≫ X.isoSpec.inv) hspec
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  have hfinite : FiniteDimensional K Γ(X, ⊤) :=
    finiteSchemeCoefficient_finite f
  exact finiteAlgebra_equiv_pi_of_full_rational_points e heinj
    ((finiteSchemeCoefficient_finrank f).trans hrank)

/-- The product coordinate indexed by a rational point is exactly the
global-section evaluation map defined by that point. -/
theorem finiteSchemeCoefficient_equiv_pi_of_full_rational_points_apply
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    {n : ℕ} (x : Fin n → (Spec (.of K) ⟶ X))
    (hxbase : ∀ i, x i ≫ f =
      Spec.map (CommRingCat.ofHom (RingHom.id K)))
    (hxinj : Function.Injective x)
    (hrank : AllCharacteristics.finiteSchemeRank f = n)
    (a : Γ(X, ⊤)) (i : Fin n) :
    letI := finiteSchemeCoefficientAlgebra f
    finiteSchemeCoefficient_equiv_pi_of_full_rational_points
      f x hxbase hxinj hrank a i =
        finiteSchemePointAlgHom f (x i) (RingHom.id K) (hxbase i) a := by
  rfl

/-- A finite scheme whose rank is exhausted by distinct rational points is
étale over the field. In the split-twelve-point route, proving the twelve
points distinct is therefore enough to obtain reducedness and étaleness. -/
theorem finiteScheme_etale_of_full_rational_points
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    {n : ℕ} (x : Fin n → (Spec (.of K) ⟶ X))
    (hxbase : ∀ i, x i ≫ f =
      Spec.map (CommRingCat.ofHom (RingHom.id K)))
    (hxinj : Function.Injective x)
    (hrank : AllCharacteristics.finiteSchemeRank f = n) : Etale f := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : IsAffine X := isAffine_of_isAffineHom f
  let e := finiteSchemeCoefficient_equiv_pi_of_full_rational_points
    f x hxbase hxinj hrank
  haveI : Algebra.Etale K Γ(X, ⊤) :=
    Algebra.Etale.of_equiv e.symm
  haveI : Etale (X.isoSpec.inv ≫ f) := by
    rw [← finiteSchemeCoefficient_spec f]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have hcomp : X.isoSpec.hom ≫ X.isoSpec.inv ≫ f = f := by simp
  rw [← hcomp]
  infer_instance

end PfaffianDescent
