var executionTreeData = [
{ name: 'method test05', open: true, prestate: {store: "?\n  Ø,\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'execute inhale i == n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce i == n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i == n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'execute inhale res == i * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce res == i * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate res == i * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate res', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate i * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
{ name: 'execute assert res == n * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'consume res == n * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate res == n * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate res', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n * n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(n -> n@1, i -> i@2, res -> res@3),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
]}
, 
{ name: 'method Ref__Mul', open: true, prestate: {store: "?\n  Ø,\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce diz != null', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz != null', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate null', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'produce n > 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n > 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'produce acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'produce diz.Ref__res == 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  Ø,\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  Ø,\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'produce acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'produce diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'produce n > 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n > 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@9 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'execute i := 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@7),\n  h(diz@4.Ref__res -> $t@8 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'execute diz.Ref__res := 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> $t@8 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> $t@8 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> $t@8 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'produce acc(diz.Ref__res, write) && (i <= n) && (diz.Ref__res == i * n) && (i < n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce acc(diz.Ref__res, write) && (i <= n) && (diz.Ref__res == i * n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce acc(diz.Ref__res, write) && (i <= n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'produce i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'produce diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
{ name: 'produce i < n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i < n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'execute diz.Ref__res := diz.Ref__res + n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate diz.Ref__res + n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'execute i := i + 1', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i + 1', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate 1', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'consume acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'consume i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'consume diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10 + 1),\n  h(diz@4.Ref__res -> $t@14 + n@5 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'consume acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'consume i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
{ name: 'consume diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> 0),\n  h(diz@4.Ref__res -> 0 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'produce acc(diz.Ref__res, write) && (i <= n) && (diz.Ref__res == i * n) && !(i < n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce acc(diz.Ref__res, write) && (i <= n) && (diz.Ref__res == i * n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce acc(diz.Ref__res, write) && (i <= n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'produce acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  Ø,\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'produce i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i <= n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'produce diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
{ name: 'produce !(i < n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate !(i < n)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i < n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
{ name: 'execute assert i == n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'consume i == n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i == n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'execute assert diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'consume diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate i * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate i', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
{ name: 'execute assert diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'consume diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
]}, 
{ name: 'consume acc(diz.Ref__res, write)', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate write', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'consume diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res == n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz.Ref__res', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate diz', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
{ name: 'evaluate n * n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}, 
{ name: 'consume n > 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n > 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""},
 children: [
{ name: 'evaluate n', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
{ name: 'evaluate 0', open: true, prestate: {store: "?\n  ?(diz -> diz@4, n -> n@5, sys__result -> sys__result@6, i -> i@10),\n  h(diz@4.Ref__res -> $t@18 # W),\n  g(diz@4.Ref__res -> $t@8 # W),\n)", heap: "", pcs: ""}}, 
]}, 
]}, 
]}
, 
]
