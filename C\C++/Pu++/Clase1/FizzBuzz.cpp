#include <iostream>

int main() {
	for (int i = 0; i <= 1000; i++) {
		if (i%5 == 0 && i%3 == 0) {
			std::cout << "FizzBuzz" << '\n';
		} else if (i%5 == 0) {
			std::cout << "Buzz" << '\n';
		} else if (i%3 == 0) {
			std::cout << "Fizz" << '\n';
		} else {
			std::cout << i << '\n';
		}
	}
	return 0;
}
