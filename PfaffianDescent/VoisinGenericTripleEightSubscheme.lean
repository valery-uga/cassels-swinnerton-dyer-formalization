import PfaffianDescent.VoisinGenericTriplePointImmersions
import AllCharacteristics.ConstantCovers
import PfaffianDescent.IntrinsicFiniteCycle

/-! The eight rational generic points as one rank-eight closed subscheme. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def genericTripleIntersectionEightEmbedding
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    (∐ fun _ : ULift.{u} (Fin 8) => Spec (.of (FractionRing R))) ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (algebraMap R (FractionRing R)))
        (q.map (algebraMap R (FractionRing R)))
        (r.map (algebraMap R (FractionRing R)))
        (hp.map (algebraMap R (FractionRing R)))
        (hq.map (algebraMap R (FractionRing R)))
        (hr.map (algebraMap R (FractionRing R)))) :=
  Sigma.desc (fun k => genericTripleIntersectionSelectedPoints
    p q r hp hq hr ell hell x hzero hnorm k.down)

/-- Relabeling the eight selected points is an isomorphism of their closed
coproduct presentations over the same triple intersection. -/
theorem genericTripleIntersectionEightEmbedding_relabel
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (σ : Equiv.Perm (Fin 8)) :
    let xr := fun k => x (σ k)
    let hzr := fun k => hzero (σ k)
    let hnr := fun k => hnorm (σ k)
    ∃ e : (∐ fun _ : ULift.{u} (Fin 8) => Spec (.of (FractionRing R))) ≅
        (∐ fun _ : ULift.{u} (Fin 8) => Spec (.of (FractionRing R))),
      e.hom ≫ genericTripleIntersectionEightEmbedding
          p q r hp hq hr ell hell x hzero hnorm =
        genericTripleIntersectionEightEmbedding
          p q r hp hq hr ell hell xr hzr hnr := by
  dsimp only
  let ε : ULift.{u} (Fin 8) ≃ ULift.{u} (Fin 8) :=
    { toFun := fun k => ⟨σ k.down⟩
      invFun := fun k => ⟨σ.symm k.down⟩
      left_inv := by intro k; cases k; simp
      right_inv := by intro k; cases k; simp }
  let e := Sigma.reindex ε
    (fun _ : ULift.{u} (Fin 8) => Spec (.of (FractionRing R)))
  refine ⟨e, ?_⟩
  apply Sigma.hom_ext
  intro k
  dsimp only [e]
  have hι : Sigma.ι (fun _ : ULift.{u} (Fin 8) =>
        Spec (.of (FractionRing R))) k ≫
        (Sigma.reindex ε (fun _ : ULift.{u} (Fin 8) =>
          Spec (.of (FractionRing R)))).hom =
      Sigma.ι (fun _ : ULift.{u} (Fin 8) =>
        Spec (.of (FractionRing R))) (ε k) := by
    simpa only [Function.comp_def] using
      (Sigma.ι_reindex_hom (ε := ε)
        (f := fun _ : ULift.{u} (Fin 8) =>
          Spec (.of (FractionRing R))) k)
  rw [← Category.assoc, hι]
  simp only [genericTripleIntersectionEightEmbedding, Sigma.ι_desc]
  rfl

theorem genericTripleIntersectionEightEmbedding_isClosedImmersion
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (hinj : Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm)) :
    IsClosedImmersion (genericTripleIntersectionEightEmbedding
      p q r hp hq hr ell hell x hzero hnorm) := by
  haveI (k : ULift.{u} (Fin 8)) : IsClosedImmersion
      (genericTripleIntersectionSelectedPoints
        p q r hp hq hr ell hell x hzero hnorm k.down) :=
    genericTripleIntersectionSelectedPoints_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm k.down
  apply AllCharacteristics.isClosedImmersion_sigmaDesc_of_disjoint_same_universe
  intro i j hij
  apply genericTripleIntersectionSelectedPoints_disjoint_ranges
    p q r hp hq hr ell hell x hzero hnorm hinj
  exact fun h => hij (ULift.down_injective h)

theorem genericTripleIntersectionEightEmbedding_toBase
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    let f := algebraMap R (FractionRing R)
    genericTripleIntersectionEightEmbedding
        p q r hp hq hr ell hell x hzero hnorm ≫
      toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f)) =
      constantCoverToBase (ULift.{u} (Fin 8))
        (Spec (.of (FractionRing R))) := by
  dsimp only
  apply Sigma.hom_ext
  intro k
  rw [← Category.assoc]
  unfold genericTripleIntersectionEightEmbedding
  rw [Sigma.ι_desc, genericTripleIntersectionSelectedPoints_toBase,
    constantCoverToBase, Sigma.ι_desc]

theorem genericTripleIntersectionEightEmbedding_rank_eight
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    let f := algebraMap R (FractionRing R)
    let i := genericTripleIntersectionEightEmbedding
      p q r hp hq hr ell hell x hzero hnorm
    let b := toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f))
    letI : IsFinite (i ≫ b) := by
      rw [genericTripleIntersectionEightEmbedding_toBase]
      exact isFinite_constantCoverToBase_spec
        (ULift.{u} (Fin 8)) (FractionRing R)
    finiteSchemeRank (i ≫ b) = 8 := by
  dsimp only
  let i := genericTripleIntersectionEightEmbedding
    p q r hp hq hr ell hell x hzero hnorm
  let b := toBase (tripleCompleteIntersectionHomogeneousIdeal
    (p.map (algebraMap R (FractionRing R)))
    (q.map (algebraMap R (FractionRing R)))
    (r.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
    (hq.map (algebraMap R (FractionRing R)))
    (hr.map (algebraMap R (FractionRing R))))
  letI : IsFinite (i ≫ b) := by
    rw [genericTripleIntersectionEightEmbedding_toBase]
    exact isFinite_constantCoverToBase_spec
      (ULift.{u} (Fin 8)) (FractionRing R)
  rw [finiteSchemeRank_eq_finrank,
    genericTripleIntersectionEightEmbedding_toBase,
    finrank_constantCoverToBase_spec]
  simp

end PfaffianDescent
