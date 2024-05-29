
import { styled, darken, lighten } from '@mui/system'

import { HEIGHT } from '../../constants/appointment';
import { useSchedulerContext } from '../../context/SchedulerProvider';

const AppointmentContainer = styled('div')((props) => {
    const {  isDragging, height, width, appointmentColor } = props;
    const { AppointmentProps } = useSchedulerContext()
    const {
       style
    } = AppointmentProps || {}

    const backgroundColor = isDragging ? 
    lighten(appointmentColor, 0.5)
    : appointmentColor

    return ({
        backgroundColor: backgroundColor,
        zIndex: '2',
        position: 'relative',
        top: 0,
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
        zIndex: 1,
        ...style
      })
});

export default AppointmentContainer