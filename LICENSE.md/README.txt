{- Universidad Simon Bolivar, Sartenejas 2018 
 Lenguajes de Programacion CI3461
 
 Demostracion de 'Theorem Proving' en Idris 1.2.0.
 Basado en la documentacion oficial de Idris. 
-}

README para TheoremProving.idr

El programa TheoremProving.idr es completamente interactivo con el usuario y aparte de requerir Idris instalado requiere la aplicacion vim, desde la cual se iran llenando paso a paso los huecos del programa hasta llegar a la demostracion.

---- INSTALACION ----
1) Instalacion de Idris
Desde el terminal correr: 
$ cabal update
$ cabal install idris

Para probar si Idris fue instalado correctamente se puede escribir en un nuevo archivo llamado hello.idr un Hello World

module Main

main : IO ()
main = putStrLn "Hello world"

Para ejecutar programas en Idris es necesario compilarlos:

$ idris hello.idr -o hello
$ ./hello
Hello world

Mas informacion en:
http://docs.idris-lang.org/en/latest/tutorial/starting.html

2) Instalacion de vim
Necesario para usar la demostracion de teoremas interactivamente.
$ sudo apt-get update
$ sudo apt-get install vim

3) Instalaion de plugins necesarios de Idris para vim
3.1) Pathogen
Necesario para poder instalar el plugin especial de Idris para Vim.
$ mkdir -p ~/.vim/autoload ~/.vim/bundle && \
$ curl -LSso ~/.vim/autoload/pathogen.vim https://tpo.pe/pathogen.vim

Mas informacion:
https://github.com/tpope/vim-pathogen


3.2) Idris-vim (una vez instalado Pathogen)
$ cd ~/.vim/bundle
$ git clone https://github.com/idris-hackers/idris-vim.git

Mas informacion:
https://github.com/idris-hackers/idris-vim

----- DESPUES DE LA INSTALACION -----
Utilizar Idris-vim
Una vez instalado, para tener una idea de como utilizar la demostracion de teoremas se puede visitar el siguiente link:
https://edwinb.wordpress.com/2013/10/28/interactive-idris-editing-with-vim/

Para abrir el archivo una vez instalado todo lo anterior, simplemente colocar en la carpeta donde se encuentre el archivo
$ idris TheoremProving.idr 
Y una vez abierto se puede comenzar a editar con :e e interactuar con los comandos de Vim
