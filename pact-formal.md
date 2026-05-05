This is the Schema self-healing rule. The crucial step is that an error in typechecking the continuation p is what drives self-healing.

Differences:
∅ |- v: \tau => ok | err(e)
raise(e)
Sigma: Now stores only errors and becomes empty on success


SUCCESS
v \in O(s, \Sigma, \tau)
∅ |- v: \tau => ok
x: Schema |- p: \tau' => ok
<\Sigma, \Pi, let x: Schema = gen s; p> -> <[], \Pi, p[v/x]>

SELF-HEAL
v \in O(s, \Sigma, Schema)
∅ |- v: Schema => ok
x: Schema |- p: \tau' => err(e)
<\Sigma, \Pi, let x: Schema = gen s; p> -> <\Sigma \cdot e, \Pi, let x: Schema = gen s; p>
