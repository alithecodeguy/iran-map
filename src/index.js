import React from 'react'
import IranMap from './IranMap'
import testData from './test-data.js'
const InteractiveIranMap = ({
  data = testData,
  height = 600,
  defaultSelectedArea = 'tehran'
}) => {
  const [state, setState] = React.useState({
    selectedArea: defaultSelectedArea
  })
  const selectAreaHandler = (area) => {
    setState((prevState) => ({ ...prevState, selectedArea: area.name }))
  }
  return (
    <IranMap
      onClick={selectAreaHandler}
      height={height}
      selectedArea={state.selectedArea}
      data={data}
    />
  )
}

export default InteractiveIranMap
