class Calculator {
  constructor(prevOperTextElem, currOperTextElem) {
    this.prevOpTxtEl = prevOperTextElem
    this.currOpTxtEl = currOperTextElem
    this.clear()
  }
  clear() {
    this.currentOperand  = ''
    this.previousOperand = ''
    this.operation = undefined
  }
  delete(){
    this.currentOperand = this.currentOperand.toString().slice(0,-1)
  }
  appendNumber(num) {
    if (num === '.' &&
        this.currentOperand.includes('.')) return
    this.currentOperand = this.currentOperand.toString() + num.toString()
  }
  chooseOperation(oper){
    if (this.currentOperand === '') return
    if (this.previousOperand !== '') {
      this.compute()
    }
    this.operation = oper
    this.previousOperand = this.currentOperand
    this.currentOperand  = ''
  }
  compute(){
    let computation
    const prev = parseFloat(this.previousOperand)
    const curr = parseFloat(this.currentOperand)
    if (isNaN(prev) || isNaN(curr)) return
    switch (this.operation) {
      case '+': computation = prev + curr 
                break
      case '-': computation = prev - curr 
                break
      case '*': computation = prev * curr 
                break
      case '/': computation = prev / curr 
                break
      default:  return
    }
    this.currentOperand = computation
    this.operation = undefined
    this.previousOperand = ''
  }
  updateDisplay() {
    this.currOpTxtEl.innerText = this.currentOperand
    if (this.operation != null) {
      this.prevOpTxtEl.innerText =
      `${this.previousOperand} ${this.operation}`
      //this.previousOperand.toString() + ' ' + this.operation.toString()
    } else {
      this.prevOpTxtEl.innerText = ''
    }
  }
}

const numberButtons    = document.querySelectorAll('[data-number]')
const operationButtons = document.querySelectorAll('[data-operation]')
const equalsButton     = document.querySelector('[data-equals]')
const deleteButton     = document.querySelector('[data-delete]')
const allClearButton   = document.querySelector('[data-all-clear]')
const prevOperText     = document.querySelector('[data-previous-operand]')
const currOperText     = document.querySelector('[data-current-operand]')

const calculator = new Calculator(prevOperText, currOperText)

numberButtons.forEach(button => {
  button.addEventListener('click', () => {
    calculator.appendNumber(button.innerText)
    calculator.updateDisplay()
  })
})
operationButtons.forEach(button => {
  button.addEventListener('click', () => {
    calculator.chooseOperation(button.innerText)
    calculator.updateDisplay()
  })
})
allClearButton.addEventListener('click', event => {
  calculator.clear()
  calculator.updateDisplay()
})
equalsButton.addEventListener('click', event => {
  calculator.compute()
  calculator.updateDisplay()
})
deleteButton.addEventListener('click', event => {
  calculator.delete()
  calculator.updateDisplay()
})
