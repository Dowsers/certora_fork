// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Counter {
    uint256 private count;

    function getCount() public view returns (uint256) {
        return count;
    }

    function increment() public {
        count += 1;
    }

    function decrement() public {
        if (count > 0) {
            count -= 1;
        }
    }
}
