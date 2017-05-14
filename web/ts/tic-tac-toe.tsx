// import * as _ from 'lodash'
import * as React from 'react'
import * as ReactDOM from 'react-dom'

// React = require('react')

// _.map(() => {}, [])

type SquareProps = {
  onClick : () => void
  value : string
}

function Square(props : SquareProps) {
  return (
    <button className="square" onClick={props.onClick}>
      {props.value}
    </button>
  )
}

type BoardProps = {
  onClick : (i : number) => void
  squares : string[]
}

type BoardState = {
}

class Board extends React.Component<BoardProps, BoardState> {
  
  renderSquare(i : number) {
    return (
      <Square
        value = {this.props.squares[i]}
        onClick = {() => this.props.onClick(i)} 
      />
    )
  }

  render() {
    const todo = [0, 1, 2]
    return (
      <div>
        {
          [0, 1, 2].map(l => {
            <div className="board-row">
            {
              [0, 1, 2].map(c => {
                console.log(`Rendering ${l} ${c}`)
                return <div>{this.renderSquare(l * 3 + c)}</div>
              })
            }
            </div>
          })
        }
      </div>
    )
  }

}

type GameProps = {

}

type Position = {
  l : number
  c : number
}

type History = {
  square : number
  squares : string[]
}

type GameState = {
  history : History[]
  stepNumber : number
  xIsNext : boolean
}

class Game extends React.Component<GameProps, GameState> {
  
  constructor() {
    super()
    this.state = {
      history : [{
        square : 0,
        squares : Array(9).fill(''),
      }],
      stepNumber : 0,
      xIsNext : true,
    }
  }

  handleClick(i : number) {
    const history = this.state.history.slice(0, this.state.stepNumber + 1)
    const current = history[history.length - 1]
    const squares = current.squares.slice()
    if (calculateWinner(squares) || squares[i]) {
      return
    }
    squares[i] = this.state.xIsNext ? 'X' : 'O'
    this.setState({
      history : history.concat([{
        square : i,
        squares : squares,
      }]),
      stepNumber : history.length,
      xIsNext : !this.state.xIsNext,
    })
  }

  jumpTo(step : number) {
    this.setState({
      stepNumber : step,
      xIsNext : !(step % 2),
    })
  }

  render() {
    const history = this.state.history
    const current = history[this.state.stepNumber]
    const winner = calculateWinner(current.squares)
 
    const moves = history.map((step, move) => {
      const { l, c } = calculateCoordinates(step.square)
      const desc =
        move
        ? `Move #${move}: (${l}, ${c})`
        : `Game start`
      const weight : "bold" | "normal" = (move == this.state.stepNumber) ? "bold" : "normal"
      const style = {
        fontWeight: weight
      }
      return (
        <li key={move}>
          <a href="#" style={style} onClick={() => this.jumpTo(move)}>{desc}</a>
        </li>
      )
    })
 
    return (
      <div className="game">
        <div className="game-board">
          <Board
            squares = {current.squares}
            onClick = {(i) => this.handleClick(i)}
           />
        </div>
        <div className="game-info">
          <div>{status}</div>
          <ol>{moves}</ol>
        </div>
      </div>
    );
  }
}

ReactDOM.render(
  <Game />,
  document.getElementById('root')
);

function calculateWinner(squares : string[]): string | null {
  const lines = [
    [0, 1, 2],
    [3, 4, 5],
    [6, 7, 8],
    [0, 3, 6],
    [1, 4, 7],
    [2, 5, 8],
    [0, 4, 8],
    [2, 4, 6],
  ]
  for (let i = 0; i < lines.length; i++) {
    const [a, b, c] = lines[i]
    if (squares[a] && squares[a] === squares[b] && squares[a] === squares[c]) {
      return squares[a]
    }
  }
  return null
}

function calculateCoordinates(i : number) : Position {
  return {
    l : 1 + Math.floor(i / 3),
    c : 1 + (i % 3),
  }
}