import React from 'react'

import TodayButton from './TodayButton'
import DateNavigation from './DateNavigation'

function NavigateDateAction() {
  return (
    <div style={{display: 'flex', alignItems: 'center'}} >
        {/* <TodayButton /> */}
        <DateNavigation />
    </div>
  )
}

export default NavigateDateAction