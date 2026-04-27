This is the Schema self-healing rule. The crucial step is that an error in typechecking the continuation p is what drives self-healing.

Differences:
\Gamma |- v: \tau => ok | err(e)
raise(e)
Sigma: Now stores only errors and becomes empty on success


SUCCESS
v \in O(s, \Sigma, \tau)
\Gamma |- v: \tau => ok
\Gamma, x: Schema |- p: \tau' => ok
<\Gamma, \Sigma, \Pi, let x: Schema = gen s; p> -> <\Gamma, [], \Pi, p[v/x]>

SELF-HEAL
v \in O(s, \Sigma, Schema)
\Gamma |- v: Schema => ok
\Gamma, x: Schema |- p: \tau' => err(e)
<\Gamma, \Sigma, \Pi, let x: Schema = gen s; p> -> <\Gamma, \Sigma \cdot e, \Pi, let x: Schema = gen s; p>
