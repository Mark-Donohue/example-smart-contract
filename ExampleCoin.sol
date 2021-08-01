// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.7.0 <0.9.0; 

/**
 * The contract houses all the logic for our coin 
 */
contract ExampleCoin {
    
    // This is the address of our wallet. It's essentially the source of the coin
    address public minter;
    // This contains the coin balances of users
    mapping (address => uint) public balances;
    
    event SentCoin(address from, address to, uint amount);
    
    constructor() {
        minter = msg.sender;
    }
    
    /**
     * Creates or 'mints' coins. Only we should be able to create coins
     */    
    function createNewCoin(address recipient, uint amount) public {
        require(msg.sender == minter);
        require(amount < 1e68);
    
        balances[recipient] += amount;
    }
    
    /**
     * Sends an amount of existing coins to a designated address
     */
    function sendCoin(address recipient, uint amount) public {
        require(amount <= balances[msg.sender], "Insufficient Balance");
        
        balances[msg.sender] -= amount;
        balances[recipient] += amount;
        emit SentCoin(msg.sender, recipient, amount);
    }
}
