#include <iostream>
using namespace std;

int main() {
	int n;
	string str;
	cin >> n;
	int a[7] = {};
	cin >> str;
	a = convertStrtoArr(str);
	for (int i = 0; i < 7; i++) {
		cout << a[i] << endl;
	}
	return 0;
}

int[] convertStrtoArr(string str) {
    // get length of string str
    int str_length = str.length();

    // create an array with size as string
    // length and initialize with 0
    int arr[str_length] = { 0 };

    int j = 0, i, sum = 0;

    // Traverse the string
    for (i = 0; str[i] != '\0'; i++) {
        // if str[i] is ' ' then split
        if (str[i] == ' ') {
            // Increment j to point to next
            // array location
            j++;
        }
        else {
            // subtract str[i] by 48 to convert it to int
            // Generate number by multiplying 10 and adding
            // (int)(str[i])
            arr[j] = arr[j] * 10 + (str[i] - 48);
        }
    }
    for (i = 0; i <= j; i++) {
        cout << arr[i] << " ";
        sum += arr[i]; // sum of array
    }

    // return sum of array
    return arr[i];
}
