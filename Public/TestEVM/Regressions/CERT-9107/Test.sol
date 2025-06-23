contract Test {
	function entry(uint[] memory nondetFp) external returns (uint) {

		assembly {
			function doThing(input, arr) -> output {
			output := add(input, mload(arr))
			}
			let d := mload(0x40)
			let a := add(d, 0x21)
			let x := add(0x100, a)
			let y := doThing(x, nondetFp)
			let b := sub(y, a)
			mstore(a, add(add(not(0x100), 1), b))
			return(a, 0x20)
		}
	}
}
