// compile -G=4

package main

import "fmt"
import "unsafe"


func F[T any]() interface{}{

	_ = func() {
		
	}
	
	type x[U any] []struct{
		t T;
		u U

		x [unsafe.Sizeof(func() (_ [0]T) {
			type uwu[T any] int
			var _ uwu[uwu[T]]
			var _ uwu[uwu[U]]
			return
		}())]int

	}

	return x[int]{}
}

var never bool

func main() {
	type x[U any] int

	if never {
		fmt.Printf("%T\n", F[float64]())
	}
}
  
