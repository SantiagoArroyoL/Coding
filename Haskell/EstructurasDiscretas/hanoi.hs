data ArbolBinario a = Hoja | Nodo a (ArbolBinario a ) (ArbolBinario a )
data NIL = ArbolBinario []

hanoi:: Int -> Int
hanoi 0 = 0
hanoi n = 2 * hanoi (n-1) +1

preorden:: ArbolBinario -> [a]
preorden NIL = []
preorden a = preorden(mktree(NIL,a,NIL))
preorden t1 a t2 = [a] ++ (preorden t1 ++ preorden t2)

postorden:: ArbolBinario -> [a]
postorden NIL = []
postorden a = postorden(mktree(NIL,a,NIL))
postorden t1 a t2 = (postorden t1 ++ postorden t2 ++ [a])

inorden:: ArbolBinario -> [a]
inorden NIL = []
inorden a = inorden(mktree(NIL,a,NIL))
inorden t1 a t2 = (inorden t1 ++ [a] ++ inorden t2)
