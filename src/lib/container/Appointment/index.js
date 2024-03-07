
import { useTheme } from '@mui/material'
import { styled, darken } from '@mui/system'

import { HEIGHT } from '../../constants/appointment';
import { useSchedulerContext } from '../../context/SchedulerProvider';
import { dragBackgroundColor } from '../../utils/theme';

const AppointmentContainer = styled('div')((props) => {
    const {  isDragging, height, width, appointmentColor } = props;
    const { AppointmentProps, color = "primary" } = useSchedulerContext()
    const {
       dragBgColor,
       style
    } = AppointmentProps || {}

    const theme = useTheme()

    const dragColor = dragBackgroundColor(theme)

    const backgroundColor = isDragging ? 
    (dragBgColor || dragColor[color]) 
    : appointmentColor

    return ({
        backgroundColor: backgroundColor,
        zIndex: '2',
        position: 'relative',
        top: 0,
        left: 0,
        borderRadius: 4,
        width: width,
        cursor: 'move',
        marginTop: '1px',
        border: '1px solid ' + darken(appointmentColor, 0.25),
        color: darken(appointmentColor, 0.7),
        overflow: 'hidden',
        whiteSpace: 'pre-wrap',
        textOverflow: 'ellipsis',
        height: height || HEIGHT + 'px',
        ...style
      })
});

export default AppointmentContainer