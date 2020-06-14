import React from 'react'
import IranMap from './IranMap'
import testData from './test-data.js'
const InteractiveIranMap = ({
  data = testData,
  height = 600,
  defaultAreasColor = '255,0,0',
  selectedAreaColor = '#00f',
  selectedAreaTextColor = '#fff',
  unselectedAreaTextColor = '#000',
  backgroundColor = '#fff',
  defaultSelectedArea = 'tehran'
}) => {
  const [state, setState] = React.useState({
    selectedArea: defaultSelectedArea
  })
  const selectAreaHandler = (area) => {
    setState((prevState) => ({ ...prevState, selectedArea: area.name }))
  }

  let arr = Object.values(data)
  let max = Math.max(...arr)

  return (
    <div>
      <IranMap
        onClick={selectAreaHandler}
        height={height}
        data={data}
        maxValue={max}
        selectedArea={state.selectedArea}
        defaultAreasColor={defaultAreasColor}
        selectedAreaColor={selectedAreaColor}
        selectedAreaTextColor={selectedAreaTextColor}
        unselectedAreaTextColor={unselectedAreaTextColor}
        backgroundColor={backgroundColor}
      />
    </div>
  )
}

export default InteractiveIranMap
