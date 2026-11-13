import json,os,glob
NEW='/home/user/src/mathport23/sources/mathlib/src'
OUT='/home/user/src/mathport23/Outputs/oleans/mathbin'
SRC='/home/user/src/shims23/src'
ir=json.load(open('/home/user/src/importRename23.json'))
def s2p(s): 
    r=''.join(x[:1].upper()+x[1:] for x in s.split('_'))
    if s.startswith('_'): r='_'+r
    if s.endswith('_'): r+='_'
    return r
missing={
 'algebra.big_operators':None,'algebra.category.Group':None,'algebra.order.ring':None,
 'analysis.convex.specific_functions':None,'analysis.special_functions.pow':None,
 'category_theory.adjunction':None,'category_theory.concrete_category':None,
 'category_theory.monoidal.of_chosen_finite_products':None,'category_theory.preadditive':None,
 'category_theory.preadditive.yoneda':None,'category_theory.shift':None,'data.set.intervals':None,
 'linear_algebra.matrix':None,'topology.algebra.group':None,'topology.algebra.infinite_sum':None,
 'topology.category.CompHaus':None,'topology.category.Profinite':None,
 'category_theory.additive.basic':['category_theory.limits.shapes.biproducts'],
}
extra={'category_theory.additive.basic':'''
/-! Compatibility shim: `category_theory.additive_category` existed in mathlib3 at
LTE's pinned commit (5947fb69, `category_theory/additive/basic.lean`) but was removed
before the end of mathlib3. Definition reproduced verbatim. -/
universe v u
namespace CategoryTheory
open CategoryTheory.Limits
/-- A preadditive category `C` is called additive if it has all finite biproducts.
See <https://stacks.math.columbia.edu/tag/0104>. -/
class AdditiveCategory (C : Type u) [Category.{v} C] extends Preadditive C, HasFiniteBiproducts C
#align category_theory.additive_category CategoryTheory.AdditiveCategory
end CategoryTheory
'''}
mods=[]
for m,repl in missing.items():
    if repl is None:
        d=os.path.join(NEW,*m.split('.'))
        repl=sorted(os.path.relpath(f,NEW)[:-6].replace('/','.') for f in glob.glob(d+'/**/*.tlean',recursive=True))
    imps=['Mathbin.'+'.'.join(s2p(c) for c in r.split('.')) for r in repl]
    mod4='Mathbin.'+'.'.join(s2p(c) for c in m.split('.'))
    p=os.path.join(SRC,*mod4.split('.'))+'.lean'
    os.makedirs(os.path.dirname(p),exist_ok=True)
    open(p,'w').write(''.join(f'import {i}\n' for i in imps)+f'\n/-! Compatibility shim: mathlib3 module `{m}` (present at LTE\'s pinned mathlib3 commit) was split/renamed before the end of mathlib3; this re-exports its successors. -/\n'+extra.get(m,''))
    t=os.path.join(NEW,*m.split('.'))+'.tlean'; os.makedirs(os.path.dirname(t),exist_ok=True)
    open(t,'a').close()
    mods.append(mod4)
open('/home/user/src/shims23/mods.txt','w').write('\n'.join(mods)+'\n')
print(len(mods))
