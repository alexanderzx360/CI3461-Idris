{- Universidad Simon Bolivar, Sartenejas 2018 
 Lenguajes de Programacion CI3461
 
 Demostracion de 'Theorem Proving' en Idris 1.2.0.
 Basado en la documentacion oficial de Idris. 
-}

module TheoremProving

{- Para los efectos de este tutorial se va a trabajar sobre una de las
funciones definida en el prelude de Idris, la cual define la adición sobre
numeros naturales, los cuales son un tipo de datos 'standalone' en Idris,
denominados 'Nat'.

plusP : Nat -> Nat -> Nat
plusP Z m = m
plusP (S k) m = S (plus k m)

Basicamente esta funcion devuelve 'm' si se le quiere sumar al numero natural
cero, representado como 'Z', o hace k llamadas recursivas a la funcion 'S k' sobre
m, la cual obtiene los 'k' sucesores de 'm', efectivamente realizando 'k + m'.

Debido a la definición de 'plus' obtenemos 2 propiedades gratuitas, sumar 'm'
con cero siempre resulta en 'm'. y sumar 'm' con cualquier numero no cero 'S k' 
siempre resulta en 'S (plus k m').

Pero como sabemos, la suma posee tambien otras propiedades utiles, por ejemplo,
la conmutatividad y la asociatividad, es decir que para nuestra funcion 'plus' se
deberia cumplir:

* Es conmutativa: para todo input Nat 'n' y 'm', plus n m = plus m n.
* Es asociativa: para todo input Nat 'n', 'm' y 'p', plus n (plus m p) = plus (plus m n) p.

Ciertamente podemos utilizar estas propiedades en un programa de Idris, pero para ello debemos
primero 'probarlas'. Antes de eso debemos hablar un poco de las 'pruebas de igualdad' en Idris.

Idris posee un tipo de igualdad proposicional (built-in propositional equility type) conceptualmente
definido como 

data (=) : a -> b -> Type where
	Refl : x = x

Establece que dos valores en dos tipos distintos 'a' y 'b' puedes ser propuestos a ser iguales. Sin
embargo hay solo una forma de probar igualdad, por reflexivilidad 'Refl'.

Un programa que habita una instancia de este tipo puede ser visto como una prueba de la proposicion
correspondiente (correspondencia Curry-Howard). Asi que trivialmente podemos probar que 4 = 4: -}

four_eq : 4 = 4
four_eq = Refl

-- Sin embargo, si intentamos probar que 4 = 5 (descomentar para que explote):

{- four_eq_five : 4 = 5
four_eq_five = Refl -}

{- Idris arroja un error durante el chequeo de tipos:

When elaborating right hand side of four_eq_five:
Type mismatch between
	x = x (Type of Refl)
and
	4 = 5 (Expected type)

Esto es debido a un importante paso durante el chequeo de tipos en Idris, denominado 'unificacion'
(unification), que se encarga de resolver argumentos implicitos como por ejemplo las 'x' en Refl. Unificar
dos terminos involucra reducirlos ambos a sus formas normales y luego verificar si existe alguna
asignacion para ellos que convierta sus formas normales iguales.

En el caso de 4 = 5, Idris intenta unificar el tipo 4 = 5 con el tipo de Refl, x = x, se da cuenta
que una solucion requiere que x sea 4 y 5 al mismo tiempo y por ende falla.

Como el chequeo de tipos involucra reducciones a formas normales, podemos escribir las siguientes
igualdades directamente: -}

twoplustwo_eq_four : 2 + 2 = 4
twoplustwo_eq_four = Refl

plus_reduces_Z : (m : Nat) -> plus Z m = m
plus_reduces_Z m = Refl

plus_reduces_Sk : (k, m : Nat) -> plus (S k) m = S (plus k m)
plus_reduces_Sk k m = Refl

{- Propiedades de 'plus' 

Usando el tipo (=), podemos declarar las propiedades de 'plus' arriba como declaraciones de 
tipos de Idris. -}

plus_commute : (n, m : Nat) -> plus n m = plus m n
plus_assoc : (n, m, p : Nat) -> plus n (plus m p) = plus (plus n m) p

{- Estas propiedad y muchas otras se encuentran probadas para la adicion de numeros naturales dentro
de la libreria estandard de Idris, usando (+) de la interfaz 'Num'. Poseen los nombres 'plusCommutative' 
y 'plusAssociative' respectivamente. 

En este punto Idris deberia quejarse que existen dos 'huecos', 'TheoremProving.plus_assoc' y 'TheoremProving.plus_commute'. Un hueco en Idris es basicamente una parte incompleta del programa, son 
utiles para escribir funciones incrementalmente, ya que podemos dejar algunas partes sin escribir y
pedirle a Idris que nos diga que es necesario para completar la definicion, como veremos adelante. 

Acontinuacion, proveemos una prueba para 'plus_commutes' directamente, escribiendo una 'pattern matching
definition' usando las capacidades de 'Theorem Proving' de Idris. Para esto utilizaremos utilidades de edicion interactiva, usando 'vim idris mode'
que provee una interfaz que le permite a vim interpretar comandos de Idris REPL. -} 

-- Creamos una declaracion de tipo:

plus_commutes1 : (n : Nat) -> (m : Nat) -> n + m = m + n

-- Creamos un 'template definition' para la prueba, presionando \d sobre la declaracion de tipo:

plus_commutes2 : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes2 n m = ?plus_commutes2_rhs

{- Como podemos observar hay un 'hueco' del lado derecho de la expresion, denotado por ?plus_commutes2_rhs.
Ahora debemos probar esto por induccion sobre n, presionando \c sobre la definicion de n tenemos: -}

plus_commutes3 : (n : Nat) -> (m : Nat) -> n + m = m + n 
plus_commutes3 Z m = ?plus_commutes3_rhs_1
plus_commutes3 (S k) m = ?plus_commutes3_rhs_2

{- Si inspeccionamos los tipos de los nuevos huecos, podemos apreciar que 'n' ha sido refinada a 'Z' y
'S k' en cada caso respectivo. Podemos hacer esto presionando \t sobre plus_commutes_rhs_1 por ejemplo, lo
cual nos da algo como:

 m : Nat
----------------------------------
plus_commutes_rhs_1 : m = plus m 0

Similarmente para plus_commutes_rhs_2:

 k : Nat
 m : Nat
----------------------------------
plus_commutes_rhs_2 : S (plus k m) = plus m (S k)

-- CASO BASE --

Podemos crear un lema separado para el caso base interactivamente, presionando \l sobre plus_commutes_Z. -}

plus_commute4_Z : m = plus m 0

plus_commutes4 : (n : Nat) -> (m : Nat) -> n + m = m + n 
plus_commutes4 Z m = plus_commute4_Z
plus_commutes4 (S k) m = ?plus_commutes4_S

{- El hueco ha sido llenado con una llamada a la funcion plus_commutes4_Z y el argumento 'm'
se ha hecho implicito ya que puede ser inferido por contexto. 

Desafortunadamente no podemos probar este lema directamente, ya que 'plus' esta definida haciendo
'matching' sobre su primer argumento, y aqui 'plus m 0' tiene un valor especifico para su segundo
argumento. De nuevo podemos probar esto por induccion, esta vez sobre m: -}

-- Creamos un 'template definition' con \d:

plus_commutes5_Z : m = plus m 0
plus_commutes5_Z = ?plus_commutes_Z_rhs

-- Como vamos a realizar induccion sobre 'm', que esta implicita, debemos traerla dentro del alcance
-- manualmente: 

plus_commutes6_Z : m = plus m 0
plus_commutes6_Z {m} = ?plus_commutes6_Z_rhs

-- Ahora hacemos induccion sobre 'm':

plus_commutes7_Z : m = plus m 0
plus_commutes7_Z {m = Z} = ?plus_commutes7_Z_rhs_1
plus_commutes7_Z {m = (S k)} = ?plus_commutes7_Z_rhs_2

{- Revisando el tipo de plus_commutes7_Z_rhs_1 muestra que puede ser probado facilmente por reflexividad:

----------------------------
plus_commutes_Z_rhs : 0 = 0

Para estas pruebas triviales, podemos hacer que Idris las escriba automaticamente presionando \o con 
el cursor sobre plus_commutes7_Z_rhs_1: -}

plus_commutes8_Z : m = plus m 0
plus_commutes8_Z {m = Z} = Refl
plus_commutes8_Z {m = (S k)} = ?plus_commutes8_Z_rhs_2

{- Sin embargo para plus_commutes8_Z_rhs_2 tenemos que:

 k : Nat
---------------------------
plus_commutes_Z_rhs_2 : S k = S (plus k 0)

Inductivamente, es obvio que k = plus k 0, podemos acceder a esta hipotesis inductiva haciendo una llamada
recursiva sobre k: -}

plus_commutes9_Z : m = plus m 0
plus_commutes9_Z {m = Z} = Refl
plus_commutes9_Z {m = (S k)} = let rec = plus_commutes9_Z {m=k} in ?plus_commutes9_Z_rhs_2

{- Ahora para plus_commutes9_Z_rhs_2 podemos ver que:

 k : Nat
 rec : k = plus k (fromInteger 0)
---------------------------
plus_commutes9_Z_rhs_2 : S k = S (plus k 0)

Sabemos que k = plus k 0, como usar esto para llegar a S k = S k?, Idris povee sintaxis de 
alto nivel para realizar reemplazos de este estilo.

rewrite prf in expr

Si tenemos prf : x = y, y el tipo requerido para expr es alguna propiedad de x, la sintaxis
rewrite ... in busca a x en el tipo requerido de expr y lo reemplaza por y. Tenemos entonces: -}

plus_commutes10_Z : m = plus m 0
plus_commutes10_Z {m = Z} = Refl
plus_commutes10_Z {m = (S k)} = let rec = plus_commutes10_Z {m=k} in rewrite rec in ?plus_commutes10_Z_rhs_2

{- Revisando de nuevo el tipo de plus_commutes10_Z_rhs_2 ahora obtenemos:

 k : Nat
 rec : k = plus k (fromInteger 0)
 _rewrite_rule : plus k 0 = k
---------------------------
plus_commutes_Z_rhs_2 : S (plus k 0) = S (plus k 0)

Usando la regla de rewrite 'rec' podemos ver que el tipo destino ha sido actualizado de 'k' a 'plus k 0'.

Ahora usando \o podemos completar la prueba: -}

plus_commutes11_Z : m = plus m 0
plus_commutes11_Z {m = Z} = Refl
plus_commutes11_Z {m = (S k)} = let rec = plus_commutes11_Z {m=k} in rewrite rec in Refl

-- El caso base ha sido demostrado.

-- CASO INDUCTIVO --

-- El teorema principal plus_commutes deberia verse de la siguiente forma:

plus_commutes11 : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes11 Z m = plus_commutes11_Z
plus_commutes11 (S k) m = ?plus_commutes11_S

{- Si observamos de nuevo el tipo de plus_commutes11_S:

 k : Nat
 m : Nat
-------------------------
plus_commutes11_S : S (plus k m) = plus m (S k)

Convenientemente, por induccion podemos decir que 'plus k m = plus m k', asi que
podemos hacer una llamada recursiva a plus_commutes: -}

plus_Commutes_Z : m = plus m 0
plus_Commutes_Z {m = Z} = Refl
plus_Commutes_Z {m = (S k)} = let rec = plus_Commutes_Z {m=k} in rewrite rec in Refl

plus_Commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_Commutes Z m = plus_Commutes_Z
plus_Commutes (S k) m = rewrite plus_Commutes k m in ?plus_Commutes_S

{- Rvisando el tipo de plus_Commutes_S:

 k : Nat
 m : Nat
 _rewrite_rule : plus m k = plus k m
------------------------
plus_Commute_S : S (plus m k) = plus m (S k)

Ahora 'm' y 'k' aparecen en el orden apropiado. Sin embargo nos falta demostrar que el simbolo
S de sucesor puede ser movido al frente del lado izquierdo de la igualdad. Por lo tanto creamos
otro lema parecido a plus_commutes_Z, luego creamos un 'template definition' y aplicamos induccion sobre m: -}

total
plus_Commutes1_S : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_Commutes1_S k Z = Refl
plus_Commutes1_S k (S j) = rewrite plus_Commutes1_S k j in Refl
 
plus_Commutes1 : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_Commutes1 Z m = plus_Commutes_Z
plus_Commutes1 (S k) m = rewrite plus_Commutes1 k m in plus_Commutes1_S k m

{- Finalmete todos los huecos han sido resueltos. La notacion 'total' significa que requerimos pasar
la funcion final al 'totality chequer', para estar seguros que termina en todos los inputs bien tipados, esto
es particularmente importante para pruebas, ya que provee una garantia que la prueba es valida para todos los casos,
no solo para aquellos donde se encuentra bien definida. Ahora que plus_Commutes posee la notacion 'total', hemos
completado la prueba de conmutatividad sobre la adicion de numeros naturales. -}





